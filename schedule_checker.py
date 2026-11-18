"""
AsanSports field schedule logic (no UI / Telegram code in here).
All user-facing text is Persian: Jalali (Shamsi) dates, Persian weekday and
month names, Persian digits.

Given a field's weekly schedule URL, e.g.
    https://api.asansports.com/v1/fields/nbzj4n/schedule?start=...&end=...
it finds the requested weekday inside that week and returns the EMPTY
(unbooked) sessions, using the field's own session length / opening hours /
prices from https://api.asansports.com/v1/fields/{field_id}/.

    service = ScheduleService()
    result = service.get_empty_slots_from_url(url, weekday=4)   # 4 = Friday
    for text in result.messages():
        print(text)

Resource notes (this runs on a small host):
- one shared HTTP session (connection reuse, gzip),
- field info cached for hours, finished day results cached for ~30 s
  (a group where several people paste the same link costs one API call),
- caches are size-bounded, no background threads.

Assumptions (unchanged from the original, adjust if wrong):
- "start"/"end" strings inside schedule items are local time (Asia/Tehran);
  only the request's start/end query params are epoch milliseconds.
- Weekdays use Python numbering: Monday=0 ... Sunday=6.
- `day_of_week` inside the field's `prices` uses the Iranian week order
  (0=Saturday ... 6=Friday).
- A price rule applies to a slot when day_of_week + exact start/end time match
  and the date is inside [effective_from, effective_to]; otherwise the field's
  base `price` is used.
"""

from __future__ import annotations

import logging
import re
import threading
import time
from dataclasses import dataclass
from html import escape as _esc
from datetime import date, datetime, time as dtime, timedelta, timezone
from typing import Optional
from urllib.parse import parse_qs, urlparse

import requests

logger = logging.getLogger(__name__)

# ---------------------------------------------------------------------------
# Configuration
# ---------------------------------------------------------------------------

try:
    from zoneinfo import ZoneInfo

    TIMEZONE = ZoneInfo("Asia/Tehran")
except Exception:  # noqa: BLE001 - no tz database on some slim hosts
    # Iran has no DST since 2022, so a fixed offset is correct for current dates.
    TIMEZONE = timezone(timedelta(hours=3, minutes=30))

DEFAULT_DURATION_MINUTES = 90
DEFAULT_WEEKDAY = 4                 # Friday
REQUEST_TIMEOUT = 10                # seconds
FIELD_INFO_TTL = 6 * 3600           # field name/hours/prices rarely change
DAY_RESULT_TTL = 30                 # keep availability fresh, still absorb duplicates
ALLOWED_HOST_SUFFIX = "asansports.com"
MAX_POLL_OPTIONS = 10               # Telegram allows 2..10 options per poll (12 on newest API)
# Always the LAST option of every poll. Telegram only shows the results after you vote,
# so people who just want to look at the votes pick this one.
VIEW_RESULTS_OPTION = "مشاهده آرا✅"

FIELD_INFO_URL_TEMPLATE = "https://api.asansports.com/v1/fields/{field_id}/"
SCHEDULE_URL_TEMPLATE = "https://api.asansports.com/v1/fields/{field_id}/schedule"

WEEKDAY_NAMES = ["Monday", "Tuesday", "Wednesday", "Thursday", "Friday", "Saturday", "Sunday"]

WEEKDAY_NAMES_FA = ["دوشنبه", "سه‌شنبه", "چهارشنبه", "پنج‌شنبه", "جمعه", "شنبه", "یکشنبه"]  # Mon..Sun
JALALI_MONTHS = ["فروردین", "اردیبهشت", "خرداد", "تیر", "مرداد", "شهریور",
                 "مهر", "آبان", "آذر", "دی", "بهمن", "اسفند"]
_FA_DIGITS = str.maketrans("0123456789,", "۰۱۲۳۴۵۶۷۸۹٬")

_FIELD_ID_RE = re.compile(r"[A-Za-z0-9_-]{1,40}")

_EN_DAYS = {
    "mon": 0, "monday": 0, "tue": 1, "tues": 1, "tuesday": 1,
    "wed": 2, "wednesday": 2, "thu": 3, "thur": 3, "thurs": 3, "thursday": 3,
    "fri": 4, "friday": 4, "sat": 5, "saturday": 5, "sun": 6, "sunday": 6,
}
# Persian names, spaces/ZWNJ removed. Longest first: "شنبه" is a substring of the others.
_FA_DAYS = (
    ("پنجشنبه", 3), ("چهارشنبه", 2), ("سهشنبه", 1), ("دوشنبه", 0),
    ("یکشنبه", 6), ("شنبه", 5), ("جمعه", 4),
)


def fa_digits(value: object) -> str:
    """12,500 -> ۱۲٬۵۰۰ (Persian digits and thousands separator)."""
    return str(value).translate(_FA_DIGITS)


def fa_price(amount: int) -> str:
    return f"{fa_digits(f'{amount:,}')} تومان"


def gregorian_to_jalali(gy: int, gm: int, gd: int) -> tuple[int, int, int]:
    """Gregorian -> Jalali (Shamsi) year, month, day. Pure arithmetic, no dependency."""
    cum = [0, 31, 59, 90, 120, 151, 181, 212, 243, 273, 304, 334]
    gy2 = gy + 1 if gm > 2 else gy
    days = (355666 + 365 * gy + (gy2 + 3) // 4 - (gy2 + 99) // 100
            + (gy2 + 399) // 400 + gd + cum[gm - 1])
    jy = -1595 + 33 * (days // 12053)
    days %= 12053
    jy += 4 * (days // 1461)
    days %= 1461
    if days > 365:
        jy += (days - 1) // 365
        days = (days - 1) % 365
    if days < 186:
        jm, jd = 1 + days // 31, 1 + days % 31
    else:
        jm, jd = 7 + (days - 186) // 30, 1 + (days - 186) % 30
    return jy, jm, jd


def format_jalali(day: date, with_weekday: bool = True) -> str:
    """date(2026, 11, 13) -> 'جمعه ۲۲ آبان ۱۴۰۵'."""
    jy, jm, jd = gregorian_to_jalali(day.year, day.month, day.day)
    text = f"{fa_digits(jd)} {JALALI_MONTHS[jm - 1]} {fa_digits(jy)}"
    return f"{WEEKDAY_NAMES_FA[day.weekday()]} {text}" if with_weekday else text


class ScheduleError(Exception):
    """A problem that is safe to show to the end user as-is."""


# ---------------------------------------------------------------------------
# Small helpers
# ---------------------------------------------------------------------------

class TTLCache:
    """Tiny thread-safe, size-bounded cache with per-entry expiry."""

    def __init__(self, ttl: float, maxsize: int = 256):
        self.ttl, self.maxsize = ttl, maxsize
        self._data: dict = {}
        self._lock = threading.Lock()

    def get(self, key):
        with self._lock:
            item = self._data.get(key)
            if item and item[0] > time.monotonic():
                return item[1]
            self._data.pop(key, None)
            return None

    def set(self, key, value) -> None:
        with self._lock:
            if len(self._data) >= self.maxsize:
                now = time.monotonic()
                for k in [k for k, (exp, _) in self._data.items() if exp <= now]:
                    del self._data[k]
                if len(self._data) >= self.maxsize:  # still full: drop the oldest
                    self._data.pop(next(iter(self._data)))
            self._data[key] = (time.monotonic() + self.ttl, value)


def weekday_from_name(name: str) -> int:
    """'Friday' / 'جمعه' -> 4. Raises ValueError on an unrecognized name."""
    cleaned = name.strip()
    try:
        return WEEKDAY_NAMES.index(cleaned.capitalize())
    except ValueError:
        day = parse_weekday(cleaned)
        if day is None:
            raise ValueError(f"نام روز نامعتبر است: {name!r}") from None
        return day


def parse_weekday(text: str) -> Optional[int]:
    """Find an English (fri / friday) or Persian (جمعه) day name in free text.
    Returns Python's weekday number (Mon=0 ... Sun=6) or None."""
    lowered = text.lower()
    for word in re.findall(r"[a-z]+", lowered):
        if word in _EN_DAYS:
            return _EN_DAYS[word]
    compact = re.sub(r"[\s\u200c\u200f]", "", lowered).replace("ي", "ی").replace("ك", "ک")
    for name, idx in _FA_DAYS:
        if name in compact:
            return idx
    return None


def current_week_window() -> tuple[int, int]:
    """(start_ms, end_ms) covering today (Tehran) + 7 days. Used when a link
    has no start/end params."""
    today = datetime.now(TIMEZONE).date()
    start = datetime(today.year, today.month, today.day, tzinfo=TIMEZONE)
    return int(start.timestamp() * 1000), int((start + timedelta(days=7)).timestamp() * 1000)


def parse_schedule_url(url: str) -> tuple[str, Optional[int], Optional[int]]:
    """Extract (field_id, start_ms, end_ms) from a public field page or API URL.

    Public pages end in ``~{field_code}``; API URLs contain
    ``/fields/{field_code}/schedule``. Missing dates are supplied by the caller.
    """
    parsed = urlparse(url.strip())
    host = (parsed.hostname or "").lower()
    if not (host == ALLOWED_HOST_SUFFIX or host.endswith("." + ALLOWED_HOST_SUFFIX)):
        raise ValueError("این لینک مربوط به آسان‌اسپورت نیست.")

    parts = [part for part in parsed.path.split("/") if part]
    field_id = None

    # API schedule URL: /v1/fields/{field_id}/schedule
    try:
        fields_index = parts.index("fields")
        if fields_index + 1 < len(parts):
            field_id = parts[fields_index + 1]
    except ValueError:
        pass

    # Public field page: /.../{localized-field-name}~{field_code}
    if field_id is None:
        last_segment = parts[-1] if parts else ""
        if "~" not in last_segment:
            raise ValueError("کد مجموعه در لینک پیدا نشد. لینک عمومی باید با ~ و سپس کد مجموعه تمام شود.")
        field_id = last_segment.rsplit("~", 1)[1]

    if not _FIELD_ID_RE.fullmatch(field_id):
        raise ValueError("کد مجموعه در لینک معتبر نیست.")

    qs = parse_qs(parsed.query)
    if "start" not in qs and "end" not in qs:
        return field_id, None, None
    try:
        start_ms = int(qs["start"][0])
        end_ms = int(qs["end"][0])
        if start_ms >= end_ms:
            raise ValueError
        return field_id, start_ms, end_ms
    except (KeyError, IndexError, ValueError) as exc:
        raise ValueError("مقادیر start/end در لینک معتبر نیستند.") from exc


def build_schedule_api_url(field_id: str, start_ms: int, end_ms: int) -> str:
    """Build the AsanSports schedule endpoint URL for a field and time window."""
    if not _FIELD_ID_RE.fullmatch(field_id):
        raise ValueError("کد مجموعه نامعتبر است.")
    if start_ms >= end_ms:
        raise ValueError("شروع بازه باید قبل از پایان آن باشد.")
    return (
        f"{SCHEDULE_URL_TEMPLATE.format(field_id=field_id)}"
        f"?start={start_ms}&end={end_ms}"
    )


# ---------------------------------------------------------------------------
# Data model
# ---------------------------------------------------------------------------

@dataclass(frozen=True)
class PriceRule:
    day_of_week: int  # Iranian week index: 0=Saturday ... 6=Friday
    start: dtime
    end: dtime
    price: int
    effective_from: date
    effective_to: date

    def covers(self, day_of_week: int, on_date: date, slot_start: dtime, slot_end: dtime) -> bool:
        return (
            self.day_of_week == day_of_week
            and self.start == slot_start
            and self.end == slot_end
            and self.effective_from <= on_date <= self.effective_to
        )


@dataclass(frozen=True)
class FieldInfo:
    id: str
    name: str
    address: str
    base_price: int
    duration_minutes: int
    day_start: dtime
    day_end: dtime            # meaningless if day_end_is_midnight is True
    day_end_is_midnight: bool
    price_rules: tuple[PriceRule, ...]

    @classmethod
    def from_api(cls, payload: dict, field_id: str = "") -> "FieldInfo":
        d = payload.get("data", payload)  # tolerate wrapped {"data": {...}} or raw dict

        def parse_hm(value: str) -> dtime:
            h, m = value.split(":")[:2]
            return dtime(int(h) % 24, int(m))

        day_end_raw = str(d.get("day_end", "24:00"))
        day_end_is_midnight = day_end_raw.strip() in ("24:00", "24:00:00")

        rules: list[PriceRule] = []
        for item in d.get("prices", []) or []:
            try:
                rules.append(
                    PriceRule(
                        day_of_week=int(item["day_of_week"]),
                        start=parse_hm(item["start"]),
                        end=parse_hm(item["end"]),
                        price=int(item["price"]),
                        effective_from=datetime.strptime(item["effective_from"], "%Y-%m-%d").date(),
                        effective_to=datetime.strptime(item["effective_to"], "%Y-%m-%d").date(),
                    )
                )
            except (KeyError, ValueError, TypeError) as exc:
                logger.warning("Skipping malformed price rule %s: %s", item, exc)

        fid = str(d.get("id") or field_id)
        return cls(
            id=fid,
            name=d.get("name") or fid,
            address=d.get("address") or "",
            base_price=int(d.get("price") or 0),
            duration_minutes=int(d.get("duration") or DEFAULT_DURATION_MINUTES),
            day_start=parse_hm(str(d.get("day_start", "07:30"))),
            day_end=dtime(0, 0) if day_end_is_midnight else parse_hm(day_end_raw),
            day_end_is_midnight=day_end_is_midnight,
            price_rules=tuple(rules),
        )


@dataclass(frozen=True)
class Slot:
    start: datetime
    end: datetime

    def __str__(self) -> str:
        return fa_digits(f"{self.start:%H:%M} - {self.end:%H:%M}")


@dataclass(frozen=True)
class PricedSlot:
    slot: Slot
    price: Optional[int]  # None if the field has no usable price data

    def __str__(self) -> str:
        if self.price is None:
            return str(self.slot)
        return f"{self.slot} ({fa_price(self.price)})"


@dataclass(frozen=True)
class DayResult:
    """Empty-slot result for one field on one specific date."""
    field: FieldInfo
    date: date
    empty_slots: tuple[PricedSlot, ...]

    def uniform_price(self) -> Optional[int]:
        """The single price if every empty slot shares it, else None."""
        prices = {s.price for s in self.empty_slots}
        if len(prices) == 1 and None not in prices:
            return next(iter(prices))
        return None

    def field_summary(self, venue=None, link: str = "", html: bool = False) -> str:
        """The text sent before the poll:

            ⚽️ hall name
            📍 آدرس: ...
            🚄 نزدیک‌ترین حمل و نقل عمومی(مترو یا BRT): ...
            🏟 نوع زمین: ...
            🌐 لینک سالن

        `venue` is any object with .size / .transit / .address / .link (see venues.py).
        Missing values are left blank. With html=True the string is Telegram-HTML
        (values escaped, the link hidden behind «لینک سالن»)."""
        esc = _esc if html else (lambda value: value)
        address = self.field.address or getattr(venue, "address", "") or ""
        transit = getattr(venue, "transit", "") or ""
        size = getattr(venue, "size", "") or ""
        link = link or getattr(venue, "link", "") or ""
        if not link:
            link_line = "🌐 "
        elif html:
            link_line = f'🌐 <a href="{_esc(link, quote=True)}">لینک سالن</a>'
        else:
            link_line = f"🌐 {link}"
        return "\n".join([
            f"⚽️ {esc(self.field.name)}",
            f"📍 آدرس: {esc(address)}",
            f"🚄 نزدیک\u200cترین حمل و نقل عمومی(مترو یا BRT): {esc(transit) or ' '}",
            f"🏟 نوع زمین: {esc(size)}",
            link_line,
        ])

    def field_summary_text(self) -> str:
        return self.field_summary()

    def slot_messages(self, combine: bool = False) -> list[str]:
        """Date header, then one message per slot (or a single message if `combine`)."""
        header = f"📅 {format_jalali(self.date)}"
        if not self.empty_slots:
            return [f"{header}\nزمان خالی وجود ندارد."]

        shared = self.uniform_price()
        if shared is not None:
            header += f"\n💰 {fa_price(shared)}"
        lines = [
            f"🕓 {s.slot}" if shared is not None else f"🕓 {s}"
            for s in self.empty_slots
        ]
        return ["\n".join([header, *lines])] if combine else [header, *lines]

    def poll_batches(self) -> list[tuple[str, list[str]]]:
        """Poll content as plain data: [(question, [option, ...]), ...].

        Telegram polls need 2..MAX_POLL_OPTIONS options. One option per poll is kept
        free for VIEW_RESULTS_OPTION (added by the caller, not included here), so slots
        are split into evenly sized batches of at most MAX_POLL_OPTIONS - 1.
        Returns [] when there are fewer than 2 slots (the caller then falls back to a
        normal text message).
        """
        slots = self.empty_slots
        if len(slots) < 2:
            return []
        price = self.uniform_price()
        price_part = f" - 💰 {fa_price(price)}" if price is not None else ""
        options = [str(s.slot) if price is not None else str(s) for s in slots]

        per_poll = MAX_POLL_OPTIONS - 1                      # last option is reserved
        batch_count = -(-len(options) // per_poll)           # ceil
        size = -(-len(options) // batch_count)               # even split, never a lone option
        header = f"📅 {format_jalali(self.date)}"

        batches = []
        for i in range(batch_count):
            chunk = options[i * size:(i + 1) * size]
            title = f"{header} ({fa_digits(i + 1)}/{fa_digits(batch_count)})" if batch_count > 1 else header
            batches.append((f"{title}{price_part}", [o[:100] for o in chunk]))
        return batches

    def messages(self, combine: bool = False) -> list[str]:
        return [self.field_summary_text(), *self.slot_messages(combine)]

    def to_text(self) -> str:
        return "\n\n".join([self.field_summary_text(), "\n".join(self.slot_messages())])


# ---------------------------------------------------------------------------
# Core service
# ---------------------------------------------------------------------------

class ScheduleService:
    """Talks to the AsanSports API and works out empty slots for one weekday.
    Thread-safe; share a single instance."""

    def __init__(self, session: Optional[requests.Session] = None):
        self.session = session or requests.Session()
        self.session.headers.setdefault("Accept", "application/json")
        self._fields = TTLCache(FIELD_INFO_TTL, maxsize=128)
        self._days = TTLCache(DAY_RESULT_TTL, maxsize=256)

    # -- public API -----------------------------------------------------------

    def get_field_info(self, field_id: str, force_refresh: bool = False) -> FieldInfo:
        info = None if force_refresh else self._fields.get(field_id)
        if info is None:
            payload = self._get_json(FIELD_INFO_URL_TEMPLATE.format(field_id=field_id), field_id=field_id)
            try:
                info = FieldInfo.from_api(payload, field_id)
            except (AttributeError, KeyError, ValueError, TypeError) as exc:
                logger.error("Bad field payload for %s: %s", field_id, exc)
                raise ScheduleError("اطلاعات دریافتی برای این مجموعه نامعتبر است.") from exc
            self._fields.set(field_id, info)
        return info

    def get_empty_slots_for_week(
        self,
        field_id: str,
        week_start_ms: int,
        week_end_ms: int,
        weekday: int = DEFAULT_WEEKDAY,
        target_date: Optional[date] = None,
    ) -> DayResult:
        """Empty sessions for one day. Pass `target_date` for an exact date, or
        `weekday` (Mon=0..Sun=6) to auto-detect it inside the given window."""
        if target_date is None:
            target_date = self._find_date_by_weekday(week_start_ms, week_end_ms, weekday)

        cache_key = (field_id, week_start_ms, week_end_ms, target_date)
        cached = self._days.get(cache_key)
        if cached is not None:
            return cached

        field_info = self.get_field_info(field_id)
        schedule_url = build_schedule_api_url(field_id, week_start_ms, week_end_ms)
        payload = self._get_json(schedule_url, field_id=field_id)
        raw_items = (payload.get("data", []) if isinstance(payload, dict) else payload) or []
        busy = [
            iv for iv in self._parse_intervals(raw_items)
            if iv[0].date() == target_date or iv[1].date() == target_date
        ]

        empty = [s for s in self._generate_day_slots(target_date, field_info) if not self._overlaps_any(s, busy)]
        result = DayResult(
            field=field_info,
            date=target_date,
            empty_slots=tuple(PricedSlot(s, self._price_for_slot(field_info, target_date, s)) for s in empty),
        )
        self._days.set(cache_key, result)
        return result

    def get_empty_slots_from_url(
        self,
        schedule_url: str,
        weekday: int = DEFAULT_WEEKDAY,
        target_date: Optional[date] = None,
    ) -> DayResult:
        """Paste in a schedule URL. Raises ValueError for a bad link and
        ScheduleError for anything that went wrong while fetching."""
        field_id, start_ms, end_ms = parse_schedule_url(schedule_url)
        if start_ms is None or end_ms is None:
            start_ms, end_ms = current_week_window()
        # Validate the endpoint and its date range before making the request.
        build_schedule_api_url(field_id, start_ms, end_ms)
        return self.get_empty_slots_for_week(field_id, start_ms, end_ms, weekday, target_date)

    # -- internals ------------------------------------------------------------

    def _get_json(self, url: str, params: Optional[dict] = None, field_id: str = ""):
        try:
            resp = self.session.get(url, params=params, timeout=REQUEST_TIMEOUT)
        except requests.RequestException as exc:
            logger.warning("API request failed (%s): %s", field_id, exc)
            raise ScheduleError("در حال حاضر دسترسی به سرور آسان‌اسپورت ممکن نیست.") from exc
        if resp.status_code == 404:
            raise ScheduleError(f"مجموعه‌ای با کد «{field_id}» پیدا نشد.")
        if not resp.ok:
            logger.warning("API returned HTTP %s for %s", resp.status_code, url)
            raise ScheduleError(f"سرور آسان‌اسپورت خطا برگرداند (HTTP {resp.status_code}).")
        try:
            return resp.json()
        except ValueError as exc:
            raise ScheduleError("پاسخ سرور آسان‌اسپورت قابل خواندن نیست.") from exc

    @staticmethod
    def _parse_intervals(raw_items: list) -> list[tuple[datetime, datetime]]:
        intervals = []
        for item in raw_items:
            try:
                intervals.append((
                    datetime.strptime(item["start"], "%Y-%m-%d %H:%M:%S"),
                    datetime.strptime(item["end"], "%Y-%m-%d %H:%M:%S"),
                ))
            except (KeyError, ValueError, TypeError) as exc:
                logger.warning("Skipping malformed schedule item %s: %s", item, exc)
        return intervals

    @staticmethod
    def _find_date_by_weekday(start_ms: int, end_ms: int, weekday: int) -> date:
        start_day = datetime.fromtimestamp(start_ms / 1000, tz=TIMEZONE).date()
        end_day = datetime.fromtimestamp(end_ms / 1000, tz=TIMEZONE).date()
        current = start_day
        while current <= end_day:
            if current.weekday() == weekday:
                return current
            current += timedelta(days=1)
        raise ScheduleError(
            f"در بازه‌ی تاریخ این لینک ({format_jalali(start_day, False)} تا {format_jalali(end_day, False)}) "
            f"«{WEEKDAY_NAMES_FA[weekday]}» وجود ندارد."
        )

    @staticmethod
    def _generate_day_slots(day: date, field_info: FieldInfo) -> list[Slot]:
        day_start_dt = datetime.combine(day, field_info.day_start)
        if field_info.day_end_is_midnight:
            day_end_dt = datetime.combine(day + timedelta(days=1), dtime(0, 0))
        else:
            day_end_dt = datetime.combine(day, field_info.day_end)
            if day_end_dt <= day_start_dt:
                day_end_dt += timedelta(days=1)

        step = timedelta(minutes=max(field_info.duration_minutes, 1))
        slots, current = [], day_start_dt
        while current + step <= day_end_dt:
            slots.append(Slot(current, current + step))
            current += step
        return slots

    @staticmethod
    def _overlaps_any(slot: Slot, intervals: list[tuple[datetime, datetime]]) -> bool:
        return any(slot.start < b_end and slot.end > b_start for b_start, b_end in intervals)

    @staticmethod
    def _price_for_slot(field_info: FieldInfo, day: date, slot: Slot) -> Optional[int]:
        iranian_dow = (day.weekday() + 2) % 7  # Python Mon=0..Sun=6 -> Iranian Sat=0..Fri=6
        start_t, end_t = slot.start.time(), slot.end.time()  # midnight wraps to 00:00
        for rule in field_info.price_rules:
            if rule.covers(iranian_dow, day, start_t, end_t):
                return rule.price
        return field_info.base_price or None
