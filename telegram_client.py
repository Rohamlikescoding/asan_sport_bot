"""
Minimal Telegram Bot API client (only `requests`, no framework).

- get_me / delete_webhook : startup checks
- get_updates             : long polling (one idle connection, ~0 CPU while waiting)
- send_message / send_many: replies, with flood-limit (429) back-off, message
                            splitting (4096 limit) and gentle pacing
- send_poll               : public (non-anonymous) multiple-answer poll, so you can
                            see who picked which time. Falls back to an anonymous
                            poll (channels only allow those), then to plain text

The bot token is never written to logs: `requests` exceptions embed the full
URL, so every error text goes through `_clean()` first.
"""

from __future__ import annotations

import html as _html
import logging
import re
import time
from dataclasses import dataclass
from typing import Any, Iterable, Optional, Union

import requests

logger = logging.getLogger(__name__)

API_URL = "https://api.telegram.org/bot{token}/{method}"
REQUEST_TIMEOUT = 15
LONG_POLL_SECONDS = 45
MESSAGE_LIMIT = 4000          # Telegram's hard limit is 4096 characters
SEND_GAP_SECONDS = 0.35       # keeps bursts well inside per-chat limits
MAX_RETRY_AFTER = 30
POLL_QUESTION_LIMIT = 300     # Telegram: question 1-300 chars
POLL_OPTION_LIMIT = 100       # Telegram: each option 1-100 chars


class HtmlText(str):
    """A message whose text is Telegram-HTML (sent with parse_mode=HTML)."""


def _strip_html(text: str) -> str:
    """Plain-text version of simple Telegram-HTML (used if Telegram rejects the markup)."""
    text = re.sub(r'<a href="([^"]*)">[^<]*</a>', lambda m: m.group(1), text)
    return _html.unescape(re.sub(r"<[^>]+>", "", text))


@dataclass(frozen=True)
class Poll:
    """A public poll (voters visible) where several options can be ticked.
    `fallback` is sent as plain text if the poll cannot be created
    (e.g. polls are disabled in that chat)."""
    question: str
    options: tuple[str, ...]
    fallback: str = ""


class TelegramError(Exception):
    def __init__(self, message: str, code: int = 0):
        super().__init__(message)
        self.code = code


class TelegramAuthError(TelegramError):
    """Bad / revoked bot token — retrying cannot help."""


def _chunks(text: str, limit: int = MESSAGE_LIMIT) -> list[str]:
    """Split on line boundaries so no message exceeds `limit` characters."""
    if len(text) <= limit:
        return [text]
    parts, current = [], ""
    for line in text.split("\n"):
        while len(line) > limit:                 # pathological single line
            if current:
                parts.append(current)
                current = ""
            parts.append(line[:limit])
            line = line[limit:]
        if current and len(current) + 1 + len(line) > limit:
            parts.append(current)
            current = line
        else:
            current = f"{current}\n{line}" if current else line
    if current:
        parts.append(current)
    return parts


class TelegramClient:
    def __init__(self, token: str, session: Optional[requests.Session] = None):
        self._token = token
        self.session = session or requests.Session()

    # -- low level ------------------------------------------------------------

    def _clean(self, value: object) -> str:
        return str(value).replace(self._token, "<token>")

    def _call(self, method: str, payload: Optional[dict] = None,
              timeout: float = REQUEST_TIMEOUT, retries: int = 3) -> Any:
        url = API_URL.format(token=self._token, method=method)
        last_error = ""
        for attempt in range(retries):
            try:
                resp = self.session.post(url, json=payload or {}, timeout=timeout)
                data = resp.json()
            except (requests.RequestException, ValueError) as exc:
                last_error = self._clean(exc)
                if attempt + 1 < retries:
                    time.sleep(1 + attempt)
                continue

            if data.get("ok"):
                return data["result"]

            code = int(data.get("error_code") or resp.status_code)
            description = data.get("description", "")
            if code == 429:
                wait = min(int((data.get("parameters") or {}).get("retry_after", 1)), MAX_RETRY_AFTER)
                logger.warning("%s: flood limit, waiting %ss", method, wait)
                time.sleep(wait + 0.5)
                last_error = description
                continue
            if code in (401, 404):
                raise TelegramAuthError(f"{method}: {description or 'invalid bot token'}", code)
            raise TelegramError(f"{method}: {code} {description}", code)

        raise TelegramError(f"{method}: gave up ({last_error})")

    # -- startup ----------------------------------------------------------------

    def get_me(self) -> dict:
        return self._call("getMe")

    def delete_webhook(self) -> None:
        """getUpdates only works while no webhook is set."""
        self._call("deleteWebhook", {"drop_pending_updates": False})

    # -- receiving ----------------------------------------------------------------

    def get_updates(self, offset: Optional[int] = None) -> list[dict]:
        payload: dict = {
            "timeout": LONG_POLL_SECONDS,
            "allowed_updates": ["message", "channel_post"],  # skip everything else
        }
        if offset is not None:
            payload["offset"] = offset
        return self._call("getUpdates", payload, timeout=LONG_POLL_SECONDS + 10, retries=1)

    # -- sending ----------------------------------------------------------------

    def send_message(self, chat_id: int | str, text: str,
                     reply_to: Optional[int] = None, thread_id: Optional[int] = None) -> bool:
        """Send `text` (auto-split if too long). Returns True if everything went out."""
        ok = True
        use_html = isinstance(text, HtmlText)
        for i, chunk in enumerate(_chunks(text)):
            payload: dict = {
                "chat_id": chat_id,
                "text": chunk,
                "link_preview_options": {"is_disabled": True},
            }
            if use_html:
                payload["parse_mode"] = "HTML"
            if thread_id:
                payload["message_thread_id"] = thread_id
            if reply_to and i == 0:
                payload["reply_parameters"] = {"message_id": reply_to, "allow_sending_without_reply": True}
            try:
                try:
                    self._call("sendMessage", payload)
                except TelegramError as exc:
                    if not (use_html and exc.code == 400):
                        raise
                    # Telegram rejected the markup: resend as plain text
                    payload.pop("parse_mode")
                    payload["text"] = _strip_html(chunk)
                    self._call("sendMessage", payload)
            except TelegramError as exc:
                logger.error("sendMessage to %s failed: %s", chat_id, self._clean(exc))
                ok = False
                if exc.code in (400, 403):  # chat gone / bot blocked / kicked
                    return False
        return ok

    def send_poll(self, chat_id: int | str, poll: Poll,
                  reply_to: Optional[int] = None, thread_id: Optional[int] = None) -> bool:
        """Send a multiple-answer poll with visible voters. Channels do not allow
        non-anonymous polls, so on a refusal it retries once as anonymous.
        Returns True on success."""
        if self._send_poll(chat_id, poll, reply_to, thread_id, anonymous=False):
            return True
        logger.info("Public poll refused in %s, retrying as anonymous", chat_id)
        return self._send_poll(chat_id, poll, reply_to, thread_id, anonymous=True)

    def _send_poll(self, chat_id: int | str, poll: Poll, reply_to: Optional[int],
                   thread_id: Optional[int], anonymous: bool) -> bool:
        payload: dict = {
            "chat_id": chat_id,
            "question": poll.question[:POLL_QUESTION_LIMIT],
            "options": [{"text": o[:POLL_OPTION_LIMIT]} for o in poll.options],
            "is_anonymous": anonymous,
            "allows_multiple_answers": True,
        }
        if thread_id:
            payload["message_thread_id"] = thread_id
        if reply_to:
            payload["reply_parameters"] = {"message_id": reply_to, "allow_sending_without_reply": True}
        try:
            self._call("sendPoll", payload)
            return True
        except TelegramError as exc:
            logger.error("sendPoll to %s failed: %s", chat_id, self._clean(exc))
            return False

    def send_many(self, chat_id: int | str, items: Iterable[Union[str, HtmlText, Poll]],
                  reply_to: Optional[int] = None, thread_id: Optional[int] = None) -> int:
        """Send several messages/polls in order. Only the first replies to `reply_to`.
        A poll that cannot be sent is replaced by its text fallback.
        Returns the number of items that failed."""
        failed = 0
        for i, item in enumerate(items):
            if i:
                time.sleep(SEND_GAP_SECONDS)
            reply = reply_to if i == 0 else None
            if isinstance(item, Poll):
                ok = self.send_poll(chat_id, item, reply, thread_id)
                if not ok and item.fallback:
                    time.sleep(SEND_GAP_SECONDS)
                    ok = self.send_message(chat_id, item.fallback, reply, thread_id)
            else:
                ok = self.send_message(chat_id, item, reply, thread_id)
            if not ok:
                failed += 1
        return failed
