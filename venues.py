"""
Venue extras the AsanSports API does not provide: court size and the nearest
metro / BRT. Kept in a small JSON file keyed by field code, so it survives
restarts and can be edited by hand or with the bot's /addvenue command.

    {"nbzj4n": {"name": "...", "size": "۴ به ۴", "transit": "مترو ...",
                "address": "", "link": "https://asansports.com/..."}}

- thread-safe, atomic writes (temp file + rename), so a crash never leaves a half-written file
- the file is re-read automatically when it changes on disk (hand edits work without a restart)
- parse_venues() understands the group-chat format the venues were shared in
"""

from __future__ import annotations

import json
import logging
import os
import re
import tempfile
import threading
from dataclasses import dataclass, fields
from typing import Optional
from urllib.parse import quote, unquote, urlparse

from schedule_checker import ALLOWED_HOST_SUFFIX, fa_digits, parse_schedule_url

logger = logging.getLogger(__name__)

# ---------------------------------------------------------------------------
# Data model
# ---------------------------------------------------------------------------


@dataclass(frozen=True)
class Venue:
    name: str = ""
    size: str = ""       # e.g. "۵ به ۵"
    transit: str = ""    # nearest metro / BRT, free text
    address: str = ""    # only used when the API has no address
    link: str = ""       # public page link (percent-encoded)

    def merged(self, new: "Venue") -> "Venue":
        """`new` wins for every field it fills in; empty fields keep the old value."""
        return Venue(**{f.name: getattr(new, f.name) or getattr(self, f.name) for f in fields(self)})


_FIELD_NAMES = {f.name for f in fields(Venue)}


# ---------------------------------------------------------------------------
# Links
# ---------------------------------------------------------------------------

def normalize_link(url: str) -> str:
    """Drop query/fragment and percent-encode the path (parentheses included),
    so the link is safe to put in a Telegram message."""
    parsed = urlparse(url.strip())
    return f"{parsed.scheme}://{parsed.netloc}{quote(unquote(parsed.path), safe='/~-_.')}"


def is_public_page_url(url: str) -> bool:
    """True for a public field page (…/name~code), False for api.* links."""
    parsed = urlparse(url.strip())
    host = (parsed.hostname or "").lower()
    if not (host == ALLOWED_HOST_SUFFIX or host.endswith("." + ALLOWED_HOST_SUFFIX)):
        return False
    if host.startswith("api."):
        return False
    parts = [p for p in parsed.path.split("/") if p]
    return bool(parts) and "~" in parts[-1]


# ---------------------------------------------------------------------------
# Parsing pasted venue messages
# ---------------------------------------------------------------------------

_URL_RE = re.compile(r"https?://[^\s<>\"']+", re.IGNORECASE)
_URL_TRAILING = ".,;:!?]}»…،؛"
# "[10/21/2026 11:16 PM] Kia: " at the start of a pasted chat line
_CHAT_PREFIX = re.compile(r"^\s*\[[^\]\n]*\d{1,2}:\d{2}[^\]\n]*\]\s*[^:\n]{1,40}:\s*")
_LEADING_SYMBOLS = re.compile(r"^[\W_]+")      # emoji, bullets, dashes...
_TRANSIT_RE = re.compile(
    r"^نزدیک[\s\u200c]*ترین[\s\u200c]*(?:مترو|ایستگاه|BRT)?[\s\u200c]*[-–—:]?\s*(.*)$", re.IGNORECASE)
_SIZE_RE = re.compile(r"(\d)\s*به\s*(\d)")
_ADDRESS_PREFIX = re.compile(r"^آدرس\s*[:：]?\s*")


def _clean_url(url: str) -> str:
    url = url.rstrip(_URL_TRAILING)
    while url.endswith(")") and url.count(")") > url.count("("):   # closing paren of [text](url)
        url = url[:-1]
    return url


def _tidy(text: str) -> str:
    text = re.sub(r"\s+", " ", text).strip()
    return re.sub(r"\s*/\s*", " / ", text)


def _build_venue(lines: list[str], link: str) -> Venue:
    name = size = transit = address = ""
    for raw in lines:
        plain = _LEADING_SYMBOLS.sub("", raw).strip()
        if not plain:
            continue
        m = _TRANSIT_RE.match(plain)
        if m:
            transit = _tidy(m.group(1))
        elif plain.lower().startswith(("مترو", "brt")):
            transit = _tidy(plain)
        elif "📍" in raw or plain.startswith("آدرس"):
            address = _tidy(_ADDRESS_PREFIX.sub("", plain))
        elif _SIZE_RE.search(plain):
            a, b = _SIZE_RE.search(plain).groups()
            size = f"{fa_digits(a)} به {fa_digits(b)}"
        elif not name:
            name = _tidy(plain)
    if transit and not re.search(r"مترو|brt", transit, re.IGNORECASE):
        transit = f"مترو {transit}"
    return Venue(
        name=name, size=size, transit=transit, address=address,
        link=normalize_link(link) if is_public_page_url(link) else "",
    )


def parse_venues(text: str) -> list[tuple[str, Venue]]:
    """Read one or many pasted venue blocks. A block ends with the line that
    holds the hall link; the lines above it give name / size / address / transit.
    Returns [(field_code, Venue), ...] in order."""
    found: list[tuple[str, Venue]] = []
    buffer: list[str] = []
    for raw in text.splitlines():
        line = _CHAT_PREFIX.sub("", raw).strip()
        if not line:
            continue
        match = _URL_RE.search(line)
        if not match:
            buffer.append(line)
            continue
        url = _clean_url(match.group())
        try:
            code, _, _ = parse_schedule_url(url)
        except ValueError:
            buffer.clear()          # not an AsanSports hall link: skip this block
            continue
        found.append((code, _build_venue(buffer, url)))
        buffer.clear()
    return found


# ---------------------------------------------------------------------------
# Store
# ---------------------------------------------------------------------------

class VenueStore:
    """JSON-file backed {field_code: Venue}. Share a single instance."""

    def __init__(self, path: str):
        self.path = path
        self._lock = threading.Lock()
        self._data: dict[str, Venue] = {}
        self._mtime: Optional[int] = None
        with self._lock:
            self._load()

    # -- reading ----------------------------------------------------------------

    def get(self, code: str) -> Optional[Venue]:
        with self._lock:
            self._reload_if_changed()
            return self._data.get(code)

    def all(self) -> dict[str, Venue]:
        with self._lock:
            self._reload_if_changed()
            return dict(self._data)

    # -- writing ----------------------------------------------------------------

    def upsert(self, code: str, venue: Venue) -> Venue:
        with self._lock:
            self._reload_if_changed()
            old = self._data.get(code)
            self._data[code] = old.merged(venue) if old else venue
            self._save()
            return self._data[code]

    def remove(self, code: str) -> bool:
        with self._lock:
            self._reload_if_changed()
            if code not in self._data:
                return False
            del self._data[code]
            self._save()
            return True

    # -- internals (call with the lock held) -------------------------------------------

    def _reload_if_changed(self) -> None:
        try:
            mtime = os.stat(self.path).st_mtime_ns
        except OSError:
            return
        if mtime != self._mtime:
            self._load()

    def _load(self) -> None:
        try:
            with open(self.path, encoding="utf-8") as fh:
                raw = json.load(fh)
            self._mtime = os.stat(self.path).st_mtime_ns
        except FileNotFoundError:
            self._data, self._mtime = {}, None
            return
        except (OSError, ValueError) as exc:
            # keep the broken file for inspection instead of overwriting it later
            logger.error("Could not read %s (%s); moved aside as .corrupt", self.path, exc)
            try:
                os.replace(self.path, self.path + ".corrupt")
            except OSError:
                pass
            self._data, self._mtime = {}, None
            return
        data: dict[str, Venue] = {}
        for code, item in (raw.items() if isinstance(raw, dict) else []):
            if isinstance(item, dict):
                data[str(code)] = Venue(**{k: str(v) for k, v in item.items() if k in _FIELD_NAMES and v is not None})
        self._data = data

    def _save(self) -> None:
        payload = {code: {f.name: getattr(v, f.name) for f in fields(Venue)} for code, v in sorted(self._data.items())}
        directory = os.path.dirname(os.path.abspath(self.path))
        os.makedirs(directory, exist_ok=True)
        fd, tmp = tempfile.mkstemp(prefix=".venues-", suffix=".tmp", dir=directory)
        try:
            with os.fdopen(fd, "w", encoding="utf-8") as fh:
                json.dump(payload, fh, ensure_ascii=False, indent=2)
                fh.write("\n")
            os.replace(tmp, self.path)
        except BaseException:
            try:
                os.unlink(tmp)
            except OSError:
                pass
            raise
        self._mtime = os.stat(self.path).st_mtime_ns
