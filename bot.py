"""
AsanSports Telegram bot
=======================
Send the bot a public AsanSports field page link (in a private chat, group, supergroup topic or
channel the bot is in); it extracts the field code and replies in the SAME chat
with the field info and a public multiple-choice POLL (you see who picked what) of the empty sessions
for the chosen day (more than 10 sessions -> several polls).

    https://api.asansports.com/v1/fields/nbzj4n/schedule?start=...&end=...
    https://api.asansports.com/v1/fields/nbzj4n/schedule?start=...&end=... saturday
    /check <link> جمعه

Day: any English (friday / fri) or Persian (جمعه) day name in the same message.
No day given -> DEFAULT_DAY (Friday).

Run:   python bot.py          (needs: pip install requests)

Settings are environment variables (all optional except the token):
    BOT_TOKEN           bot token from @BotFather
    DEFAULT_DAY         Friday
    USE_POLL            1 = empty sessions as a public multi-answer poll (default), 0 = text only
    COMBINE_SLOTS       text mode only: 0 = one message per slot, 1 = one message for all slots
    ALLOWED_CHAT_IDS    comma-separated chat ids allowed to use the bot (empty = everyone)
    MAX_WORKERS         3     parallel requests being served
    MAX_URLS            5     links processed per message
    COOLDOWN_SECONDS    2     per-user pause between requests
    VENUES_FILE         venues.json next to bot.py: nearest metro / court size per hall
    ADMIN_IDS           comma-separated Telegram user ids allowed to use /addvenue, /delvenue,
                        /venues (empty = those commands are disabled). /myid shows your id.

Venue commands (admins):
    /addvenue <paste one or more hall messages>   adds / updates halls (see HELP below)
    /delvenue <hall link or code>
    /venues
    LOG_LEVEL           INFO
"""

from __future__ import annotations

import logging
import os
import re
import signal
import sys
import threading
import time
from concurrent.futures import ThreadPoolExecutor
from typing import Optional, Union

from schedule_checker import (
    DEFAULT_WEEKDAY, ScheduleError, ScheduleService, VIEW_RESULTS_OPTION, WEEKDAY_NAMES_FA,
    fa_digits, parse_schedule_url, parse_weekday, weekday_from_name,
)
from telegram_client import HtmlText, Poll, TelegramAuthError, TelegramClient, TelegramError
from venues import VenueStore, is_public_page_url, normalize_link, parse_venues

# ---------------------------------------------------------------------------
# Settings
# ---------------------------------------------------------------------------

# Set BOT_TOKEN in the environment. Never commit or hardcode the bot token.
BOT_TOKEN = os.environ.get("BOT_TOKEN", "").strip()


def _env_int(name: str, default: int) -> int:
    try:
        return int(os.environ.get(name, default))
    except ValueError:
        return default


COMBINE_SLOTS = os.environ.get("COMBINE_SLOTS", "0").strip().lower() in ("1", "true", "yes")
USE_POLL = os.environ.get("USE_POLL", "1").strip().lower() in ("1", "true", "yes")
MAX_WORKERS = max(1, _env_int("MAX_WORKERS", 3))
MAX_URLS = max(1, _env_int("MAX_URLS", 5))
COOLDOWN_SECONDS = max(0, _env_int("COOLDOWN_SECONDS", 2))
MAX_PENDING = MAX_WORKERS * 4           # requests waiting beyond this are refused politely
VENUES_FILE = os.environ.get("VENUES_FILE") or os.path.join(os.path.dirname(os.path.abspath(__file__)), "venues.json")
ADMIN_IDS = {
    int(x) for x in os.environ.get("ADMIN_IDS", "").replace(" ", "").split(",")
    if x.lstrip("-").isdigit()
}
ALLOWED_CHAT_IDS = {
    int(x) for x in os.environ.get("ALLOWED_CHAT_IDS", "").replace(" ", "").split(",")
    if x.lstrip("-").isdigit()
}

try:
    DEFAULT_DAY = weekday_from_name(os.environ.get("DEFAULT_DAY", "Friday"))
except ValueError:
    DEFAULT_DAY = DEFAULT_WEEKDAY

HELP_TEXT = (
    "👋 لینک صفحه‌ی یک مجموعه‌ی ورزشی آسان‌اسپورت را بفرستید تا زمان‌های خالی آن را "
    "به‌صورت نظرسنجی برایتان بفرستم.\n\n"
    "مثال:\n"
    "https://asansports.com/مجموعه-های-ورزشی/چمن-مصنوعی-شکوفه~8kbpg8\n\n"
    f"📅 برای انتخاب روز، نام روز را کنار لینک بنویسید (پیش‌فرض: {WEEKDAY_NAMES_FA[DEFAULT_DAY]}):\n"
    "<لینک> شنبه   یا   <لینک> saturday\n\n"
    f"در هر پیام تا {fa_digits(MAX_URLS)} لینک می‌توانید بفرستید.\n\n"
    f"🗳 آخرین گزینه‌ی هر نظرسنجی «{VIEW_RESULTS_OPTION}» است؛ اگر فقط می‌خواهید آرا را ببینید، "
    "همین گزینه را انتخاب کنید."
)

ADDVENUE_HELP = (
    "ℹ️ بعد از /addvenue پیام سالن (یا چند سالن) را paste کنید. هر سالن باید لینکش را داشته باشد:\n\n"
    "🔸 نام سالن\n"
    "✅ سالن ۵ به ۵\n"
    "🔻 نزدیک ترین مترو - مترو ...\n"
    "🔹 https://asansports.com/...~کد\n\n"
    "حذف: /delvenue <لینک یا کد>\n"
    "فهرست: /venues"
)

logger = logging.getLogger("bot")

_URL_RE = re.compile(r"https?://[^\s<>\"']+", re.IGNORECASE)
_URL_TRAILING = ".,;:!?)]}»…،؛"


# ---------------------------------------------------------------------------
# Message parsing
# ---------------------------------------------------------------------------

def extract_urls(text: str, entities: list[dict]) -> list[str]:
    """Plain links in the text plus hidden links behind formatted text."""
    found = [m.group().rstrip(_URL_TRAILING) for m in _URL_RE.finditer(text)]
    found += [e["url"] for e in entities if e.get("type") == "text_link" and e.get("url")]
    return list(dict.fromkeys(found))  # de-duplicate, keep order


# ---------------------------------------------------------------------------
# Bot
# ---------------------------------------------------------------------------

class Bot:
    def __init__(self, client: TelegramClient, service: ScheduleService, venues: VenueStore):
        self.client = client
        self.service = service
        self.venues = venues
        self.username = ""
        self.stop = threading.Event()

        self._pool = ThreadPoolExecutor(max_workers=MAX_WORKERS, thread_name_prefix="req")
        self._lock = threading.Lock()
        self._pending = 0
        self._last_request: dict[tuple, float] = {}
        self._chat_locks: dict[int, threading.Lock] = {}

    # -- main loop --------------------------------------------------------------

    def run(self) -> int:
        try:
            me = self.client.get_me()
            self.username = me.get("username", "")
            self.client.delete_webhook()
        except TelegramAuthError as exc:
            logger.critical("Telegram rejected the bot token (%s). Check BOT_TOKEN.", exc)
            return 1
        except TelegramError as exc:
            logger.critical("Could not reach Telegram at startup: %s", exc)
            return 1

        logger.info("Started as @%s (workers=%d, poll=%s)", self.username, MAX_WORKERS, USE_POLL)
        offset: Optional[int] = None
        backoff = 1

        while not self.stop.is_set():
            try:
                updates = self.client.get_updates(offset)
                backoff = 1
            except TelegramAuthError as exc:
                logger.critical("Bot token no longer valid: %s", exc)
                return 1
            except TelegramError as exc:
                if exc.code == 409:
                    logger.error("Another instance is polling with this token. Retrying in 10 s.")
                    self.stop.wait(10)
                else:
                    logger.warning("Polling error: %s (retry in %ss)", exc, backoff)
                    self.stop.wait(backoff)
                    backoff = min(backoff * 2, 60)
                continue

            for update in updates:
                offset = update["update_id"] + 1
                msg = update.get("message") or update.get("channel_post")
                if msg:
                    self._dispatch(msg)

        logger.info("Stopping...")
        self._pool.shutdown(wait=True, cancel_futures=True)
        return 0

    def _dispatch(self, msg: dict) -> None:
        with self._lock:
            if self._pending >= MAX_PENDING:
                overloaded = True
            else:
                overloaded = False
                self._pending += 1
        if overloaded:
            logger.warning("Overloaded, refusing a request")
            self.client.send_message(msg["chat"]["id"], "⏳ الان سرم شلوغ است؛ لطفاً چند لحظه دیگر دوباره تلاش کنید.",
                                     reply_to=msg.get("message_id"))
            return
        self._pool.submit(self._run_handler, msg)

    def _run_handler(self, msg: dict) -> None:
        try:
            self._handle(msg)
        except Exception:  # noqa: BLE001 - one bad message must never kill the bot
            logger.exception("Unhandled error while handling a message")
        finally:
            with self._lock:
                self._pending -= 1

    # -- request handling ---------------------------------------------------------

    def _handle(self, msg: dict) -> None:
        chat = msg.get("chat") or {}
        chat_id = chat.get("id")
        sender = msg.get("from") or {}
        text = (msg.get("text") or msg.get("caption") or "").strip()
        if chat_id is None or not text or sender.get("is_bot"):
            return
        if ALLOWED_CHAT_IDS and chat_id not in ALLOWED_CHAT_IDS:
            return

        private = chat.get("type") == "private"
        first = text.split(None, 1)[0]
        is_command = first.startswith("/")
        if is_command:
            name, _, target = first[1:].partition("@")
            if target and target.lower() != self.username.lower():
                return  # command meant for another bot
            if name.lower() in ("start", "help"):
                self._reply(msg, [HELP_TEXT])
                return
            if name.lower() == "myid":
                self._reply(msg, [f"🆔 {sender.get('id', '—')}"])
                return
            if name.lower() in ("addvenue", "delvenue", "venues"):
                self._venue_command(msg, name.lower(), text[len(first):].strip())
                return

        entities = msg.get("entities") or msg.get("caption_entities") or []
        urls = extract_urls(text, entities)

        valid, problems = [], []
        for url in urls:
            try:
                parse_schedule_url(url)
                valid.append(url)
            except ValueError as exc:
                problems.append(str(exc))

        if not valid:
            # Stay quiet in groups unless the person clearly addressed the bot.
            if private or is_command:
                note = problems[0] if problems else "لینکی در پیام شما پیدا نکردم."
                self._reply(msg, [f"⚠️ {note}\n\nبرای دیدن مثال، /help را بفرستید."])
            return

        if not self._cooldown_ok((chat_id, sender.get("id", chat_id))):
            logger.info("Cooldown: ignored a request in chat %s", chat_id)
            return

        weekday = parse_weekday(_URL_RE.sub(" ", text))
        if weekday is None:
            weekday = DEFAULT_DAY

        outgoing: list[Union[str, HtmlText, Poll]] = []
        if len(valid) > MAX_URLS:
            outgoing.append(f"ℹ️ فقط {fa_digits(MAX_URLS)} لینک اول بررسی شد.")
            valid = valid[:MAX_URLS]

        for url in valid:
            try:
                result = self.service.get_empty_slots_from_url(url, weekday=weekday)
                code = parse_schedule_url(url)[0]
                link = normalize_link(url) if is_public_page_url(url) else ""
                outgoing.extend(self._render(result, self.venues.get(code), link))
            except (ScheduleError, ValueError) as exc:
                outgoing.append(f"⚠️ {exc}")
            except Exception:  # noqa: BLE001
                logger.exception("Failed to process %s", url)
                outgoing.append("⚠️ هنگام خواندن این لینک مشکلی پیش آمد.")

        self._reply(msg, outgoing)

    # -- helpers --------------------------------------------------------------------

    @staticmethod
    def _render(result, venue=None, link: str = "") -> list[Union[str, HtmlText, Poll]]:
        """Hall info text, then the empty sessions as poll(s) (or text)."""
        out: list[Union[str, HtmlText, Poll]] = [HtmlText(result.field_summary(venue, link, html=True))]
        batches = result.poll_batches() if USE_POLL else []
        if not batches:  # polls off, no slots, or just one slot (a poll needs 2+ options)
            out.extend(result.slot_messages(combine=COMBINE_SLOTS))
            return out
        for question, options in batches:
            fallback = "\n".join([question, *(f"🕓 {o}" for o in options)])
            out.append(Poll(question, (*options, VIEW_RESULTS_OPTION), fallback))
        return out

    def _venue_command(self, msg: dict, command: str, args: str) -> None:
        sender_id = (msg.get("from") or {}).get("id")
        if not ADMIN_IDS or sender_id not in ADMIN_IDS:
            note = "⛔ این دستور فقط برای ادمین‌هاست."
            if not ADMIN_IDS:
                note += "\n(متغیر ADMIN_IDS روی سرور تنظیم نشده است.)"
            self._reply(msg, [note])
            return

        if command == "venues":
            venues = self.venues.all()
            if not venues:
                self._reply(msg, ["هنوز سالنی ذخیره نشده است."])
                return
            lines = [f"{code} | {v.name or '—'} | {v.size or '—'} | {v.transit or '—'}" for code, v in venues.items()]
            self._reply(msg, [f"📋 {fa_digits(len(venues))} سالن:\n" + "\n".join(lines)])
            return

        if command == "delvenue":
            target = args.split(None, 1)[0] if args else ""
            if not target:
                self._reply(msg, ["لینک یا کد سالن را بعد از /delvenue بنویسید."])
                return
            try:
                code = parse_schedule_url(target)[0] if "/" in target else target
            except ValueError as exc:
                self._reply(msg, [f"⚠️ {exc}"])
                return
            done = self.venues.remove(code)
            self._reply(msg, [f"🗑 {code} حذف شد." if done else f"سالنی با کد {code} پیدا نشد."])
            return

        # /addvenue
        parsed = parse_venues(args)
        if not parsed:
            self._reply(msg, [ADDVENUE_HELP])
            return
        lines = []
        for code, venue in parsed:
            saved = self.venues.upsert(code, venue)
            lines.append(f"✅ {saved.name or code} ({code}) - {saved.size or '—'} - {saved.transit or 'بدون مترو'}")
        self._reply(msg, [f"{fa_digits(len(parsed))} سالن ذخیره شد:\n" + "\n".join(lines)])

    def _reply(self, msg: dict, texts: list[Union[str, HtmlText, Poll]]) -> None:
        chat_id = msg["chat"]["id"]
        thread_id = msg.get("message_thread_id") if msg.get("is_topic_message") else None
        # One chat is served by one thread at a time, so messages from two
        # simultaneous requests never interleave.
        with self._chat_lock(chat_id):
            failed = self.client.send_many(chat_id, texts, reply_to=msg.get("message_id"), thread_id=thread_id)
        if failed:
            logger.warning("%d message(s) failed to send in chat %s", failed, chat_id)

    def _chat_lock(self, chat_id: int) -> threading.Lock:
        with self._lock:
            if len(self._chat_locks) > 1000:  # keep memory bounded
                self._chat_locks = {k: v for k, v in self._chat_locks.items() if v.locked()}
            return self._chat_locks.setdefault(chat_id, threading.Lock())

    def _cooldown_ok(self, key: tuple) -> bool:
        if not COOLDOWN_SECONDS:
            return True
        now = time.monotonic()
        with self._lock:
            if now - self._last_request.get(key, 0.0) < COOLDOWN_SECONDS:
                return False
            self._last_request[key] = now
            if len(self._last_request) > 2000:
                self._last_request = {k: t for k, t in self._last_request.items() if now - t < 60}
        return True


# ---------------------------------------------------------------------------
# Entry point
# ---------------------------------------------------------------------------

def main() -> int:
    logging.basicConfig(
        level=os.environ.get("LOG_LEVEL", "INFO").upper(),
        format="%(asctime)s [%(levelname)s] %(message)s",
    )
    logging.getLogger("urllib3").setLevel(logging.WARNING)  # its debug lines contain the token

    if not BOT_TOKEN or ":" not in BOT_TOKEN:
        logger.critical("No bot token set. Define the BOT_TOKEN variable (get one from @BotFather).")
        return 1

    bot = Bot(TelegramClient(BOT_TOKEN), ScheduleService(), VenueStore(VENUES_FILE))

    def _shutdown(signum, _frame):
        logger.info("Signal %s received", signum)
        bot.stop.set()

    signal.signal(signal.SIGINT, _shutdown)
    signal.signal(signal.SIGTERM, _shutdown)
    return bot.run()


if __name__ == "__main__":
    sys.exit(main())
