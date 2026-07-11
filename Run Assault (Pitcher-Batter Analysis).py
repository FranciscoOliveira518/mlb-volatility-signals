from __future__ import annotations

import argparse
import json
from datetime import datetime, timedelta, timezone
from typing import Any, Optional
from math import sqrt
from pathlib import Path
import re
import unicodedata
from zoneinfo import ZoneInfo

import requests
import statsapi
from bs4 import BeautifulSoup

try:
    import pandas as pd
except Exception as exc:
    pd = None
    PANDAS_IMPORT_ERROR = str(exc)
else:
    PANDAS_IMPORT_ERROR = None

try:
    from pybaseball import statcast_batter, statcast_pitcher
except Exception as exc:
    statcast_pitcher = None
    statcast_batter = None
    PYBASEBALL_IMPORT_ERROR = str(exc)
else:
    PYBASEBALL_IMPORT_ERROR = None


LOOKAHEAD_HOURS = 10
LOOKBACK_HOURS = 2
MLB_STATS_API_BASE = "https://statsapi.mlb.com/api/v1"
BASEBALL_SAVANT_CUSTOM_LEADERBOARD_BASE = "https://baseballsavant.mlb.com/leaderboard/custom"
DEFAULT_SEASON_START_MONTH_DAY = "03-01"
REGULAR_SEASON_GAME_TYPE = "R"
BPS_PA_RELIABILITY_TARGET = 50
BPS_PITCH_RELIABILITY_TARGET = 150
DEFAULT_LINEUP_SLOT_WEIGHTS = {
    1: 1.25,
    2: 1.25,
    3: 1.25,
    4: 1.25,
    5: 1.05,
    6: 1.05,
    7: 0.85,
    8: 0.85,
    9: 0.85,
}
RUN_ASSAULT_WEIGHTED_LINEUP_SCALE = 120.0
RUN_ASSAULT_BEST_4_CLUSTER_SCALE = 35.0
RUN_ASSAULT_MAIN_PITCH_SCALE = 18.0
RUN_ASSAULT_BEST_3_CLUSTER_SCALE = 35.0

# --- Half-Inning Volatility Analysis constants (tunable) ---
HALF_INNING_SEGMENT_SIZE = 5
# Damage aggregate (section 2): ISO scale (.250 ISO -> ~100) and missing fallback.
HALF_INNING_ISO_SCALE = 0.250
HALF_INNING_NEUTRAL_SCORE = 50.0
# Extension-risk component weights (section 4.1). Core terms sum to 0.80; the two
# optional uplifts fill the remaining budget so contact and pitcher weakness matter.
HALF_INNING_EXTENSION_WEIGHTS = {
    "pressure_next_3": 0.30,
    "pressure_next_5": 0.25,
    "strongest_2_pressure": 0.20,
    "turnover_bonus": 0.15,
    "weak_out_risk": -0.10,
}
HALF_INNING_EXTENSION_CONTACT_WEIGHT = 0.10
HALF_INNING_EXTENSION_PITCHER_WEAKNESS_WEIGHT = 0.10
# Run-conversion-risk component weights (section 4.2).
HALF_INNING_CONVERSION_WEIGHTS = {
    "damage_next_3": 0.30,
    "damage_next_5": 0.30,
    "power_after_traffic": 0.20,
    "speed_baserunning": 0.10,
    "double_play_penalty": -0.10,
}
HALF_INNING_CONVERSION_PITCHER_WEAKNESS_WEIGHT = 0.10
# Final-volatility weights (section 4.3).
HALF_INNING_VOLATILITY_WEIGHTS = {
    "extension_risk": 0.40,
    "run_conversion_risk": 0.35,
    "p_6plus": 0.15,
    "turnover_bonus": 0.10,
}
# Lineup-turnover bonus magnitudes (0-~20 scale so the 0.15 weight matters).
HALF_INNING_TURNOVER_SLOT1_MID = 10.0       # slot 1 lands in position 4 or 5
HALF_INNING_TURNOVER_BOTTOM_TO_TOP = 18.0   # starts 7/8/9 and reaches slot 1 or 2
# PA-extension probability bands: (base, divisor, low, high).
HALF_INNING_P4_BAND = (0.35, 180.0, 0.20, 0.85)
HALF_INNING_P5_BAND = (0.18, 220.0, 0.08, 0.65)
HALF_INNING_P6_BAND = (0.08, 300.0, 0.03, 0.45)
# Section-4 classification bands.
HALF_INNING_LOW_THRESHOLD = 40.0
HALF_INNING_HIGH_THRESHOLD = 60.0
# Fallbacks for unavailable inputs.
HALF_INNING_SPEED_NEUTRAL = 50.0
HALF_INNING_DOUBLE_PLAY_DEFAULT = 0.0
# Game-profile weights (section 5).
HALF_INNING_GAME_WEIGHTS = {
    "avg": 0.40,
    "min": 0.35,
    "max": 0.15,
    "asymmetry": -0.10,
}
BURST_MAGNITUDE_BLEND_WEIGHT = 0.65   # w: weight on burst component vs run-assault risk
BURST_COUNT_TO_100_SCALE = 25.0       # rescales expected_burst_count (~0-4) onto 0-100

BALL_DESCRIPTIONS = {"ball", "blocked_ball"}
CALLED_STRIKE_DESCRIPTIONS = {"called_strike"}
INTENTIONAL_BALL_DESCRIPTIONS = {"intent_ball", "pitchout"}
IN_ZONE_NUMBERS = {1, 2, 3, 4, 5, 6, 7, 8, 9}
OUT_OF_ZONE_NUMBERS = {11, 12, 13, 14}

ZONE_PCT_GOOD = 52.0
ZONE_PCT_BAD = 38.0
CHASE_PCT_GOOD = 32.0
CHASE_PCT_BAD = 20.0
CALLED_STRIKE_PCT_GOOD = 20.0
CALLED_STRIKE_PCT_BAD = 12.0
BALL_PCT_GOOD = 30.0
BALL_PCT_BAD = 45.0

PSCORE_WEIGHT_RUN_PREVENTION = 0.30
PSCORE_WEIGHT_SWING_MISS = 0.20
PSCORE_WEIGHT_DAMAGE_CONTROL = 0.20
PSCORE_WEIGHT_WALK_CONTROL = 0.10
PSCORE_WEIGHT_CONTACT_QUALITY = 0.15
PSCORE_WEIGHT_PITCH_SHAPE = 0.05

BASEBALL_SAVANT_DEFAULT_BATTER_FIELDS = [
    "pa",
    "k_percent",
    "bb_percent",
    "slg_percent",
    "on_base_percent",
    "isolated_power",
    "xba",
    "xslg",
    "xwoba",
    "sweet_spot_percent",
    "barrel_batted_rate",
    "hard_hit_percent",
    "avg_best_speed",
    "avg_hyper_speed",
    "whiff_percent",
    "swing_percent",
    "sprint_speed",
]

BASEBALL_SAVANT_HEADERS = {
    "User-Agent": (
        "Mozilla/5.0 (Windows NT 10.0; Win64; x64) "
        "AppleWebKit/537.36 (KHTML, like Gecko) "
        "Chrome/124.0 Safari/537.36"
    ),
    "Referer": "https://baseballsavant.mlb.com/",
    "Accept": "text/csv,application/json,text/plain,*/*",
}

STATCAST_COLUMNS = [
    "game_date",
    "game_type",
    "pitcher",
    "player_name",
    "pitch_type",
    "pitch_name",
    "stand",
    "p_throws",
    "release_speed",
    "release_spin_rate",
    "release_extension",
    "plate_x",
    "plate_z",
    "zone",
    "description",
    "events",
    "type",
    "balls",
    "strikes",
    "launch_speed",
    "launch_angle",
    "estimated_woba_using_speedangle",
    "woba_value",
    "estimated_ba_using_speedangle",
    "estimated_slg_using_speedangle",
    "hit_distance_sc",
    "bb_type",
    "delta_run_exp",
]

HIT_EVENTS = {"single", "double", "triple", "home_run"}
XBH_EVENTS = {"double", "triple", "home_run"}
HOME_RUN_EVENTS = {"home_run"}
STRIKEOUT_EVENTS = {"strikeout", "strikeout_double_play"}
WALK_EVENTS = {"walk", "intent_walk"}
NON_AB_EVENTS = {"walk", "intent_walk", "hit_by_pitch", "sac_bunt", "sac_fly", "catcher_interf"}
WHIFF_DESCRIPTIONS = {"swinging_strike", "swinging_strike_blocked", "missed_bunt"}
SWING_DESCRIPTIONS = {
    "swinging_strike",
    "swinging_strike_blocked",
    "missed_bunt",
    "foul",
    "foul_tip",
    "foul_bunt",
    "hit_into_play",
    "hit_into_play_score",
    "hit_into_play_no_out",
}
BATTER_HAND_SPLITS = [
    ("overall", None, "Overall"),
    ("vs RHB", "R", "Right-handed batters"),
    ("vs LHB", "L", "Left-handed batters"),
]


def build_baseball_savant_batter_leaderboard_url(
    season: int,
    fields: list[str] | None = None,
    min_pa: int = 10,
) -> str:
    selections = ",".join(fields or BASEBALL_SAVANT_DEFAULT_BATTER_FIELDS)
    return (
        f"{BASEBALL_SAVANT_CUSTOM_LEADERBOARD_BASE}"
        f"?year={season}"
        f"&type=batter"
        f"&filter="
        f"&min={min_pa}"
        f"&selections={selections}"
        f"&chart=false"
        f"&x=pa"
        f"&y=pa"
        f"&r=no"
        f"&chartType=beeswarm"
        f"&sort=xwoba"
        f"&sortDir=desc"
    )


TEAM_NAME_ALIASES = {
    "athletics": ["oakland athletics", "oakland as", "oakland a's", "athletics", "as", "a's", "ath", "oak"],
    "los angeles angels": ["los angeles angels", "la angels", "angels", "los angeles angels of anaheim", "laa", "ana"],
    "houston astros": ["houston astros", "astros", "hou"],
    "toronto blue jays": ["toronto blue jays", "blue jays", "tor"],
    "atlanta braves": ["atlanta braves", "braves", "atl"],
    "milwaukee brewers": ["milwaukee brewers", "brewers", "mil"],
    "st louis cardinals": ["st louis cardinals", "st. louis cardinals", "cardinals", "stl"],
    "chicago cubs": ["chicago cubs", "cubs"],
    "arizona diamondbacks": ["arizona diamondbacks", "diamondbacks", "d-backs", "dbacks", "ari", "az"],
    "los angeles dodgers": ["los angeles dodgers", "la dodgers", "dodgers", "lad"],
    "san francisco giants": ["san francisco giants", "giants", "sf giants", "sfg", "sf"],
    "cleveland guardians": ["cleveland guardians", "guardians", "cle"],
    "seattle mariners": ["seattle mariners", "mariners", "sea"],
    "miami marlins": ["miami marlins", "marlins", "mia", "florida marlins"],
    "new york mets": ["new york mets", "mets", "nym"],
    "washington nationals": ["washington nationals", "nationals", "nats", "wsh", "was"],
    "baltimore orioles": ["baltimore orioles", "orioles", "bal"],
    "san diego padres": ["san diego padres", "padres", "sdp", "sd"],
    "philadelphia phillies": ["philadelphia phillies", "phillies", "phi"],
    "pittsburgh pirates": ["pittsburgh pirates", "pirates", "pit"],
    "texas rangers": ["texas rangers", "rangers", "tex"],
    "tampa bay rays": ["tampa bay rays", "rays", "tbr", "tb"],
    "boston red sox": ["boston red sox", "red sox", "bos"],
    "cincinnati reds": ["cincinnati reds", "reds", "cin"],
    "colorado rockies": ["colorado rockies", "rockies", "col"],
    "kansas city royals": ["kansas city royals", "royals", "kcr", "kc"],
    "detroit tigers": ["detroit tigers", "tigers", "det"],
    "minnesota twins": ["minnesota twins", "twins", "min"],
    "chicago white sox": ["chicago white sox", "white sox", "chw", "cws"],
    "new york yankees": ["new york yankees", "yankees", "nyy"],
}

TEAM_ABBREV_TO_CANONICAL = {
    "ATH": "athletics",
    "LAA": "los angeles angels",
    "HOU": "houston astros",
    "TOR": "toronto blue jays",
    "ATL": "atlanta braves",
    "MIL": "milwaukee brewers",
    "STL": "st louis cardinals",
    "CHC": "chicago cubs",
    "AZ": "arizona diamondbacks",
    "ARI": "arizona diamondbacks",
    "LAD": "los angeles dodgers",
    "SF": "san francisco giants",
    "SFG": "san francisco giants",
    "CLE": "cleveland guardians",
    "SEA": "seattle mariners",
    "MIA": "miami marlins",
    "NYM": "new york mets",
    "WSH": "washington nationals",
    "WAS": "washington nationals",
    "BAL": "baltimore orioles",
    "SD": "san diego padres",
    "SDP": "san diego padres",
    "PHI": "philadelphia phillies",
    "PIT": "pittsburgh pirates",
    "TEX": "texas rangers",
    "TB": "tampa bay rays",
    "TBR": "tampa bay rays",
    "BOS": "boston red sox",
    "CIN": "cincinnati reds",
    "COL": "colorado rockies",
    "KC": "kansas city royals",
    "KCR": "kansas city royals",
    "DET": "detroit tigers",
    "MIN": "minnesota twins",
    "CWS": "chicago white sox",
    "CHW": "chicago white sox",
    "NYY": "new york yankees",
}

TEAM_ALIAS_LOOKUP: dict[str, str] = {}
for canonical_name, aliases in TEAM_NAME_ALIASES.items():
    TEAM_ALIAS_LOOKUP[canonical_name] = canonical_name
    for alias in aliases:
        TEAM_ALIAS_LOOKUP[alias] = canonical_name

_MATCHUP_SEP_RE = re.compile(r"\s+(?:@|at|vs\.?|versus)\s+", re.IGNORECASE)

_MLB_PAGE_HEADERS = {
    "User-Agent": (
        "Mozilla/5.0 (Windows NT 10.0; Win64; x64) "
        "AppleWebKit/537.36 (KHTML, like Gecko) "
        "Chrome/124.0.0.0 Safari/537.36"
    ),
    "Accept": "text/html,application/xhtml+xml,application/xml;q=0.9,image/avif,image/webp,*/*;q=0.8",
    "Accept-Language": "en-US,en;q=0.9",
    "Referer": "https://www.mlb.com/",
}


def normalize_text(value: str | None) -> str:
    if not value:
        return ""
    text = unicodedata.normalize("NFKD", value)
    text = "".join(ch for ch in text if not unicodedata.combining(ch))
    text = text.lower().strip()
    text = re.sub(r"[^\w\s%/,\.-]", "", text)
    return re.sub(r"\s+", " ", text)


def normalize_line(text: str | None) -> str:
    return re.sub(r"\s+", " ", (text or "").strip())


def canonicalize_team_name(team_name: str | None) -> str:
    normalized = normalize_text(team_name)
    if not normalized:
        return ""
    return TEAM_ALIAS_LOOKUP.get(normalized, normalized)


def canonicalize_team_name_from_page(team_name: str | None) -> str:
    if not team_name:
        return ""

    normalized = normalize_text(team_name)
    if normalized in TEAM_ALIAS_LOOKUP:
        return TEAM_ALIAS_LOOKUP[normalized]

    upper = re.sub(r"[^A-Z]", "", team_name.upper())
    if upper in TEAM_ABBREV_TO_CANONICAL:
        return TEAM_ABBREV_TO_CANONICAL[upper]

    return normalized


def split_matchup_title(title: str | None) -> tuple[Optional[str], Optional[str]]:
    if not title:
        return None, None

    text = normalize_line(title)
    match = _MATCHUP_SEP_RE.search(text)
    if not match:
        return None, None

    away = text[: match.start()].strip()
    home = text[match.end() :].strip()
    if not away or not home:
        return None, None

    return away, home


def canonicalize_matchup_title(title: str | None) -> tuple[Optional[str], Optional[str]]:
    away_raw, home_raw = split_matchup_title(title)
    if not away_raw or not home_raw:
        return None, None

    return canonicalize_team_name_from_page(away_raw), canonicalize_team_name_from_page(home_raw)


def expand_team_canonicals(canon: str) -> set[str]:
    alts: set[str] = {canon}
    target = TEAM_ALIAS_LOOKUP.get(canon, canon)
    alts.add(target)

    for norm, resolved in TEAM_ALIAS_LOOKUP.items():
        if resolved == target:
            alts.add(norm)
            alts.add(resolved)

    return {alt for alt in alts if alt}


def fuzzy_match_in_lookup(
    away_canon: str,
    home_canon: str,
    lookup: dict[tuple[str, str], Any],
) -> Optional[tuple[str, str]]:
    if (away_canon, home_canon) in lookup:
        return (away_canon, home_canon)

    for away_alt in expand_team_canonicals(away_canon):
        for home_alt in expand_team_canonicals(home_canon):
            if (away_alt, home_alt) in lookup:
                return (away_alt, home_alt)

    return None


def parse_game_datetime_utc(game: dict[str, Any]) -> datetime | None:
    for value in (game.get("game_datetime"), game.get("game_date"), game.get("datetime")):
        if not value or not isinstance(value, str):
            continue

        text = value.strip()
        if text.endswith("Z"):
            text = text[:-1] + "+00:00"

        try:
            dt = datetime.fromisoformat(text)
        except ValueError:
            continue

        if dt.tzinfo is None:
            dt = dt.replace(tzinfo=timezone.utc)
        return dt.astimezone(timezone.utc)

    return None


def get_games_for_date(date_str: str) -> list[dict[str, Any]]:
    games = []
    seen_game_ids: set[Any] = set()

    for game in statsapi.schedule(date=date_str):
        game_id = game.get("game_id")
        if game_id in seen_game_ids:
            continue

        seen_game_ids.add(game_id)
        game["parsed_game_datetime_utc"] = parse_game_datetime_utc(game)
        games.append(game)

    return sorted(games, key=lambda g: g.get("parsed_game_datetime_utc") or datetime.max.replace(tzinfo=timezone.utc))


def get_games_starting_within_window(
    lookahead_hours: int = LOOKAHEAD_HOURS,
    lookback_hours: int = LOOKBACK_HOURS,
) -> list[dict[str, Any]]:
    now_utc = datetime.now(timezone.utc)
    window_start_utc = now_utc - timedelta(hours=lookback_hours)
    window_end_utc = now_utc + timedelta(hours=lookahead_hours)

    dates_to_fetch = {
        window_start_utc.date().isoformat(),
        now_utc.date().isoformat(),
        window_end_utc.date().isoformat(),
    }
    window_games: list[dict[str, Any]] = []
    seen_game_ids: set[Any] = set()

    for date_str in sorted(dates_to_fetch):
        for game in statsapi.schedule(date=date_str):
            game_dt = parse_game_datetime_utc(game)
            if game_dt is None or not (window_start_utc <= game_dt <= window_end_utc):
                continue

            game_id = game.get("game_id")
            if game_id in seen_game_ids:
                continue

            seen_game_ids.add(game_id)
            game["parsed_game_datetime_utc"] = game_dt
            window_games.append(game)

    return sorted(window_games, key=lambda g: g["parsed_game_datetime_utc"])


def get_games_starting_within_next_hours(hours: int = LOOKAHEAD_HOURS) -> list[dict[str, Any]]:
    return get_games_starting_within_window(lookahead_hours=hours, lookback_hours=0)


def choose_best_player_match(player_name: str, matches: list[dict[str, Any]]) -> Optional[dict[str, Any]]:
    wanted = normalize_text(player_name)

    for row in matches:
        full_name = normalize_text(row.get("fullName") or row.get("nameFirstLast"))
        if full_name == wanted:
            return row

    for row in matches:
        display_name = normalize_text(row.get("fullFMLName") or row.get("fullName"))
        if display_name == wanted:
            return row

    for row in matches:
        if row.get("active") is True:
            return row

    return matches[0] if matches else None


def get_pitcher_id(pitcher_name: str | None) -> tuple[Optional[int], Optional[str]]:
    if not pitcher_name or pitcher_name == "TBD":
        return None, "No announced probable pitcher."

    try:
        matches = statsapi.lookup_player(pitcher_name)
    except Exception as exc:
        return None, f"statsapi.lookup_player failed for {pitcher_name}: {exc}"

    best = choose_best_player_match(pitcher_name, matches or [])
    if not best:
        return None, f"No MLBAM player ID found for {pitcher_name}."

    player_id = best.get("id")
    if not player_id:
        return None, f"Player match for {pitcher_name} had no id."

    return int(player_id), None


def build_starting_lineups_url_from_game_dt(game_dt_utc: datetime | None) -> str:
    eastern = ZoneInfo("America/New_York")
    target_dt = game_dt_utc.astimezone(eastern) if game_dt_utc else datetime.now(eastern)
    return f"https://www.mlb.com/starting-lineups/{target_dt.date().isoformat()}"


def fetch_starting_lineups_page_html(game_dt_utc: datetime | None) -> tuple[Optional[str], Optional[str], Optional[str]]:
    url = build_starting_lineups_url_from_game_dt(game_dt_utc)
    session = requests.Session()
    session.headers.update(_MLB_PAGE_HEADERS)

    try:
        session.get("https://www.mlb.com/", timeout=15)
        response = session.get(url, timeout=20)
        response.raise_for_status()
        return response.text, url, None
    except Exception as exc:
        return None, url, f"Failed to fetch MLB starting lineups page {url}: {exc}"


def fetch_game_live_feed(game_pk: int) -> tuple[Optional[dict[str, Any]], Optional[str]]:
    candidates = [
        f"https://statsapi.mlb.com/api/v1.1/game/{game_pk}/feed/live",
        f"{MLB_STATS_API_BASE}/game/{game_pk}/feed/live",
    ]
    last_exc: Exception | None = None

    for url in candidates:
        try:
            response = requests.get(url, timeout=20)
            if response.status_code == 404:
                last_exc = Exception(f"404 Not Found: {url}")
                continue
            response.raise_for_status()
            return response.json(), None
        except Exception as exc:
            last_exc = exc

    return None, f"Failed to fetch live game feed for gamePk={game_pk}: {last_exc}"


def extract_team_lineup_from_live_feed(live_feed: dict[str, Any], side: str) -> dict[str, Any]:
    result = {
        "source": "MLB live game feed",
        "side": side,
        "status": "unknown",
        "reason": None,
        "players": [],
    }

    boxscore_teams = (((live_feed.get("liveData") or {}).get("boxscore") or {}).get("teams") or {})
    team_block = boxscore_teams.get(side) or {}
    batting_order = team_block.get("battingOrder") or []
    players = team_block.get("players") or {}

    if not batting_order:
        result["reason"] = f"No batting order published yet for {side} team."
        return result

    extracted_players = []
    for order_index, player_ref in enumerate(batting_order, start=1):
        player_key = f"ID{player_ref}" if not str(player_ref).startswith("ID") else str(player_ref)
        player_block = players.get(player_key) or {}
        person = player_block.get("person") or {}
        position = (player_block.get("position") or {}).get("abbreviation", "N/A")
        status_desc = ((player_block.get("status") or {}).get("description")) or "N/A"

        extracted_players.append(
            {
                "batting_order": order_index,
                "player_id": person.get("id"),
                "name": person.get("fullName", "N/A"),
                "position": position,
                "status": status_desc,
            }
        )

    result["status"] = "announced"
    result["players"] = extracted_players
    return result


def get_game_lineups_from_live_feed(game_pk: int) -> dict[str, Any]:
    live_feed, reason = fetch_game_live_feed(game_pk)
    if live_feed is None:
        empty = {
            "source": "MLB live game feed",
            "status": "unknown",
            "reason": reason,
            "players": [],
        }
        return {"away": {**empty, "side": "away"}, "home": {**empty, "side": "home"}}

    return {
        "away": extract_team_lineup_from_live_feed(live_feed, "away"),
        "home": extract_team_lineup_from_live_feed(live_feed, "home"),
    }


def extract_raw_matchup_title_from_node(matchup_node) -> str | None:
    away_node = matchup_node.select_one(".starting-lineups__team-name--away")
    at_node = matchup_node.select_one(".starting-lineups__team-name--at")
    home_node = matchup_node.select_one(".starting-lineups__team-name--home")

    away = away_node.get_text(" ", strip=True) if away_node else ""
    at = at_node.get_text(" ", strip=True) if at_node else "@"
    home = home_node.get_text(" ", strip=True) if home_node else ""

    if not away or not home:
        return None

    return normalize_line(f"{away} {at} {home}")


def find_matchup_card_container(matchup_node):
    current = matchup_node
    while current is not None:
        if getattr(current, "name", None):
            has_title = current.select_one("div.starting-lineups__team-names") is not None
            has_teams_block = current.select_one("div.starting-lineups__teams") is not None
            if has_title and has_teams_block:
                return current
        current = current.parent
    return None


def extract_team_players_from_ol(team_ol) -> dict[str, Any]:
    result = {
        "status": "unknown",
        "reason": None,
        "players": [],
    }

    if team_ol is None:
        result["reason"] = "Team lineup container not found in MLB starting-lineups HTML."
        return result

    full_text = normalize_line(team_ol.get_text(" ", strip=True))
    player_items = team_ol.select("li.starting-lineups__player")

    players: list[dict[str, Any]] = []
    for batting_order, li in enumerate(player_items, start=1):
        player_link = li.select_one("a.starting-lineups__player--link")
        position_span = li.select_one("span.starting-lineups__player--position")

        name = normalize_line(player_link.get_text(" ", strip=True) if player_link else "")
        position = normalize_line(position_span.get_text(" ", strip=True) if position_span else "N/A")

        if name and name.upper() != "TBD":
            players.append(
                {
                    "batting_order": batting_order,
                    "player_id": None,
                    "name": name,
                    "position": position,
                    "status": "announced",
                }
            )

    if players:
        result["status"] = "announced"
        result["players"] = players
        return result

    if "TBD" in full_text.upper():
        result["status"] = "tbd"
        result["reason"] = "Lineup still listed as TBD on MLB starting-lineups page."
        return result

    result["reason"] = "No player rows extracted and lineup was not explicitly marked TBD."
    return result


def build_announced_lineups_lookup_from_html(page_html: str) -> dict[tuple[str, str], dict[str, Any]]:
    soup = BeautifulSoup(page_html, "html.parser")
    lookup: dict[tuple[str, str], dict[str, Any]] = {}

    for matchup_node in soup.select("div.starting-lineups__team-names"):
        raw_title = extract_raw_matchup_title_from_node(matchup_node)
        if not raw_title:
            continue

        away_canon, home_canon = canonicalize_matchup_title(raw_title)
        if not away_canon or not home_canon:
            continue

        matchup_card = find_matchup_card_container(matchup_node)
        teams_block = matchup_card.select_one("div.starting-lineups__teams") if matchup_card else None
        away_ol = teams_block.select_one("ol.starting-lineups__team--away") if teams_block else None
        home_ol = teams_block.select_one("ol.starting-lineups__team--home") if teams_block else None

        lookup[(away_canon, home_canon)] = {
            "raw_matchup_header": raw_title,
            "away_team": away_canon,
            "home_team": home_canon,
            "away_lineup": extract_team_players_from_ol(away_ol),
            "home_lineup": extract_team_players_from_ol(home_ol),
        }

    return lookup


def is_matchup_header(line: str) -> bool:
    return bool(_MATCHUP_SEP_RE.search(line)) and not line.startswith("http")


def is_lineup_label(line: str) -> bool:
    return bool(re.match(r"^[A-Z]{2,3}\s+Lineup$", line))


def is_batter_line(line: str) -> bool:
    return bool(re.match(r"^\d+\.\s+.+$", line))


def extract_batter_name_from_line(line: str) -> str:
    match = re.match(r"^\d+\.\s+(.+?)\s+\(([RLS])\)\s+[A-Z0-9]+$", line)
    if match:
        return match.group(1).strip()

    match = re.match(r"^\d+\.\s+(.+?)\s+\([RLS]\)", line)
    if match:
        return match.group(1).strip()

    match = re.match(r"^\d+\.\s+(.+?)\s+[A-Z]{1,3}$", line)
    if match:
        return match.group(1).strip()

    return re.sub(r"^\d+\.\s*", "", line).strip()


def parse_single_lineup_section(lines: list[str], label_idx: int) -> tuple[list[str], str, int]:
    names: list[str] = []
    i = label_idx + 1

    while i < len(lines):
        line = lines[i]

        if is_lineup_label(line) or is_matchup_header(line):
            break

        if line == "TBD":
            return [], "tbd", i + 1

        if is_batter_line(line):
            names.append(extract_batter_name_from_line(line))

        i += 1

    if names:
        return names, "announced", i

    return [], "unknown", i


def find_first_two_lineup_labels_after_header(lines: list[str], start_idx: int) -> list[tuple[int, str]]:
    labels: list[tuple[int, str]] = []

    for i in range(start_idx + 1, len(lines)):
        line = lines[i]
        if is_matchup_header(line):
            break
        if is_lineup_label(line):
            labels.append((i, line))
            if len(labels) == 2:
                break

    return labels


def text_lineup_entry(names: list[str], status: str) -> dict[str, Any]:
    if status == "tbd":
        return {"status": "tbd", "reason": "Lineup TBD on MLB page.", "players": []}
    if not names:
        return {"status": "unknown", "reason": "No batter names extracted.", "players": []}

    return {
        "status": "announced",
        "reason": None,
        "players": [
            {
                "batting_order": idx,
                "player_id": None,
                "name": name,
                "position": "N/A",
                "status": "announced",
            }
            for idx, name in enumerate(names, start=1)
        ],
    }


def build_announced_lineups_lookup_from_text(page_html: str) -> dict[tuple[str, str], dict[str, Any]]:
    soup = BeautifulSoup(page_html, "html.parser")
    lines = [normalize_line(line) for line in soup.get_text("\n", strip=True).splitlines()]
    lines = [line for line in lines if line]

    lookup: dict[tuple[str, str], dict[str, Any]] = {}
    i = 0

    while i < len(lines):
        line = lines[i]
        if not is_matchup_header(line):
            i += 1
            continue

        away_raw, home_raw = split_matchup_title(line)
        if not away_raw or not home_raw:
            i += 1
            continue

        labels = find_first_two_lineup_labels_after_header(lines, i)
        if len(labels) < 2:
            i += 1
            continue

        away_label_idx, _ = labels[0]
        home_label_idx, _ = labels[1]
        away_names, away_status, _ = parse_single_lineup_section(lines, away_label_idx)
        home_names, home_status, next_idx = parse_single_lineup_section(lines, home_label_idx)

        away_canon = canonicalize_team_name_from_page(away_raw)
        home_canon = canonicalize_team_name_from_page(home_raw)
        lookup[(away_canon, home_canon)] = {
            "raw_matchup_header": line,
            "away_team": away_canon,
            "home_team": home_canon,
            "away_lineup": text_lineup_entry(away_names, away_status),
            "home_lineup": text_lineup_entry(home_names, home_status),
        }

        i = max(next_idx, i + 1)

    return lookup


def build_announced_lineups_lookup(games: list[dict[str, Any]]) -> dict[tuple[str, str], dict[str, Any]]:
    pages_by_url: dict[str, str] = {}
    lookup: dict[tuple[str, str], dict[str, Any]] = {}

    for game in games:
        game_dt = game.get("parsed_game_datetime_utc")
        url = build_starting_lineups_url_from_game_dt(game_dt)

        if url not in pages_by_url:
            page_html, _, fetch_err = fetch_starting_lineups_page_html(game_dt)
            if not page_html:
                print(f"[WARN] {fetch_err}")
                pages_by_url[url] = ""
            else:
                pages_by_url[url] = page_html

        page_html = pages_by_url[url]
        if not page_html:
            continue

        page_lookup = build_announced_lineups_lookup_from_html(page_html)
        if not page_lookup:
            page_lookup = build_announced_lineups_lookup_from_text(page_html)

        lookup.update(page_lookup)

    return lookup


def get_announced_lineup_names_for_game(
    away_team: str | None,
    home_team: str | None,
    announced_lookup: dict[tuple[str, str], dict[str, Any]],
) -> dict[str, Any]:
    away_canon = canonicalize_team_name(away_team)
    home_canon = canonicalize_team_name(home_team)

    item = announced_lookup.get((away_canon, home_canon))
    match_method = "exact"

    if item is None:
        fuzzy_key = fuzzy_match_in_lookup(away_canon, home_canon, announced_lookup)
        if fuzzy_key is not None:
            item = announced_lookup[fuzzy_key]
            match_method = "fuzzy_alias"

    if item is not None:
        return {
            "source": "MLB starting lineups page",
            "match_method": match_method,
            "reason": None,
            "raw_matchup_header": item.get("raw_matchup_header"),
            "away_lineup_status": item["away_lineup"]["status"],
            "home_lineup_status": item["home_lineup"]["status"],
            "away_lineup_reason": item["away_lineup"].get("reason"),
            "home_lineup_reason": item["home_lineup"].get("reason"),
            "away_lineup_players": item["away_lineup"].get("players", []),
            "home_lineup_players": item["home_lineup"].get("players", []),
        }

    return {
        "source": "MLB starting lineups page",
        "match_method": None,
        "reason": (
            f"No MLB lineup block matched scheduled game {away_team} @ {home_team}. "
            f"Searched key: ({away_canon!r}, {home_canon!r})."
        ),
        "raw_matchup_header": None,
        "away_lineup_status": "not_found",
        "home_lineup_status": "not_found",
        "away_lineup_reason": None,
        "home_lineup_reason": None,
        "away_lineup_players": [],
        "home_lineup_players": [],
    }


def choose_lineup(
    announced_players: list[dict[str, Any]],
    announced_status: str,
    announced_reason: str | None,
    live_lineup: dict[str, Any],
) -> dict[str, Any]:
    if announced_players:
        return {
            "source": "MLB starting lineups page",
            "status": announced_status,
            "reason": announced_reason,
            "players": announced_players,
        }

    live_players = live_lineup.get("players") or []
    if live_players:
        return {
            "source": live_lineup.get("source", "MLB live game feed"),
            "status": live_lineup.get("status", "announced"),
            "reason": live_lineup.get("reason"),
            "players": live_players,
        }

    return {
        "source": "none",
        "status": announced_status or live_lineup.get("status") or "unknown",
        "reason": announced_reason or live_lineup.get("reason"),
        "players": [],
    }


def safe_float(value: Any, default: Optional[float] = None) -> Optional[float]:
    if value in (None, "", "N/A"):
        return default
    try:
        if pd is not None and pd.isna(value):
            return default
        return float(value)
    except Exception:
        return default


def safe_div(numerator: Any, denominator: Any) -> float:
    num = safe_float(numerator, 0.0) or 0.0
    den = safe_float(denominator, 0.0) or 0.0
    if den == 0:
        return float("nan")
    return num / den


def clamp(value: float, low: float = 0.0, high: float = 100.0) -> float:
    if value != value:
        return value
    return max(low, min(high, value))


def score_lower_is_better(value: Any, good: float, bad: float) -> float:
    v = safe_float(value)
    if v is None:
        return float("nan")
    return clamp(100.0 * (bad - v) / (bad - good))


def score_higher_is_better(value: Any, bad: float, good: float) -> float:
    v = safe_float(value)
    if v is None:
        return float("nan")
    return clamp(100.0 * (v - bad) / (good - bad))


def weighted_score(parts: list[tuple[float, float]]) -> float:
    usable = [(score, weight) for score, weight in parts if score == score]
    if not usable:
        return float("nan")
    total_weight = sum(weight for _, weight in usable)
    return sum(score * weight for score, weight in usable) / total_weight


def mode_value(series: Any) -> Any:
    if pd is None or series is None:
        return None
    clean = series.dropna()
    if clean.empty:
        return None
    modes = clean.mode()
    if modes.empty:
        return clean.iloc[0]
    return modes.iloc[0]


def normalize_event(value: Any) -> str:
    if value is None:
        return ""
    if pd is not None and pd.isna(value):
        return ""
    return str(value).strip()


def normalize_hand_code(value: Any) -> Any:
    if value is None:
        return pd.NA if pd is not None else None
    if pd is not None and pd.isna(value):
        return pd.NA

    text = str(value).strip().upper()
    if text in {"R", "RIGHT", "RHB", "RIGHT-HANDED"}:
        return "R"
    if text in {"L", "LEFT", "LHB", "LEFT-HANDED"}:
        return "L"
    if text in {"S", "SWITCH"}:
        return "S"
    return text or (pd.NA if pd is not None else None)


def hand_split_label(hand_code: str | None) -> str:
    if hand_code == "R":
        return "Right-handed batters"
    if hand_code == "L":
        return "Left-handed batters"
    return "Overall"


def normalize_statcast_dataframe(df: Any) -> Any:
    if pd is None:
        return None
    if df is None or df.empty:
        return pd.DataFrame(columns=STATCAST_COLUMNS)

    out = df.copy()
    for column in STATCAST_COLUMNS:
        if column not in out.columns:
            out[column] = pd.NA

    for column in [
        "release_speed",
        "release_spin_rate",
        "release_extension",
        "plate_x",
        "plate_z",
        "zone",
        "balls",
        "strikes",
        "launch_speed",
        "launch_angle",
        "estimated_woba_using_speedangle",
        "woba_value",
        "estimated_ba_using_speedangle",
        "estimated_slg_using_speedangle",
        "hit_distance_sc",
        "delta_run_exp",
    ]:
        out[column] = pd.to_numeric(out[column], errors="coerce")

    out["stand"] = out["stand"].apply(normalize_hand_code)
    out["p_throws"] = out["p_throws"].apply(normalize_hand_code)
    out["game_type"] = out["game_type"].astype("string").str.strip().str.upper()
    out["pitch_type"] = out["pitch_type"].astype("string").str.strip().str.upper()
    out["pitch_type"] = out["pitch_type"].where(out["pitch_type"].notna(), pd.NA)

    return out


def filter_regular_season_statcast_dataframe(df: Any) -> Any:
    if pd is None or df is None or df.empty or "game_type" not in df.columns:
        return df

    has_game_type = df["game_type"].notna() & (df["game_type"].astype(str).str.strip() != "")
    if not bool(has_game_type.any()):
        return df

    return df[df["game_type"] == REGULAR_SEASON_GAME_TYPE].copy()


def fetch_pitcher_statcast_data(pitcher_id: int, start_date: str, end_date: str) -> Any:
    if pd is None:
        print(f"[WARN] pandas unavailable; cannot process Statcast data: {PANDAS_IMPORT_ERROR}")
        return None
    if statcast_pitcher is None:
        print(f"[WARN] pybaseball unavailable; cannot fetch Statcast data: {PYBASEBALL_IMPORT_ERROR}")
        return pd.DataFrame(columns=STATCAST_COLUMNS)

    try:
        df = statcast_pitcher(start_date, end_date, pitcher_id)
    except Exception as exc:
        print(f"[WARN] Statcast fetch failed for pitcher_id={pitcher_id}: {exc}")
        return pd.DataFrame(columns=STATCAST_COLUMNS)

    return filter_regular_season_statcast_dataframe(normalize_statcast_dataframe(df))


def season_start_for_end_date(end_date: str) -> str:
    year = int(end_date[:4])
    return f"{year}-{DEFAULT_SEASON_START_MONTH_DAY}"


PLAYER_PROFILE_CACHE: dict[int, dict[str, Any]] = {}
BATTER_STATCAST_CACHE: dict[tuple[int, str, str, str | None], Any] = {}


def normalize_batting_side(value: Any) -> str | None:
    hand = normalize_hand_code(value)
    if hand in {"R", "L", "S"}:
        return str(hand)
    return None


def fetch_player_profile(player_id: int | None) -> dict[str, Any]:
    if not player_id:
        return {}
    if player_id in PLAYER_PROFILE_CACHE:
        return PLAYER_PROFILE_CACHE[player_id]

    url = f"{MLB_STATS_API_BASE}/people/{player_id}"
    try:
        response = requests.get(url, timeout=20)
        response.raise_for_status()
        people = (response.json() or {}).get("people") or []
        profile = people[0] if people else {}
    except Exception as exc:
        profile = {"_error": f"Failed to fetch player profile for {player_id}: {exc}"}

    PLAYER_PROFILE_CACHE[player_id] = profile
    return profile


def get_player_batting_side(player_id: int | None) -> str | None:
    profile = fetch_player_profile(player_id)
    return normalize_batting_side(((profile.get("batSide") or {}).get("code")))


def get_player_pitch_hand(player_id: int | None) -> str | None:
    profile = fetch_player_profile(player_id)
    return normalize_batting_side(((profile.get("pitchHand") or {}).get("code")))


def resolve_player_id(player_name: str | None, existing_player_id: Any = None) -> tuple[int | None, str | None]:
    if existing_player_id:
        try:
            return int(existing_player_id), None
        except Exception:
            pass

    if not player_name or player_name == "N/A":
        return None, "Missing player name."

    try:
        matches = statsapi.lookup_player(player_name)
    except Exception as exc:
        return None, f"statsapi.lookup_player failed for {player_name}: {exc}"

    best = choose_best_player_match(player_name, matches or [])
    if not best or not best.get("id"):
        return None, f"No MLBAM player ID found for {player_name}."

    return int(best["id"]), None


def effective_batter_hand_for_pitcher(batting_side: str | None, opponent_pitcher_hand: str | None) -> str | None:
    if batting_side in {"R", "L"}:
        return batting_side
    if batting_side == "S" and opponent_pitcher_hand == "R":
        return "L"
    if batting_side == "S" and opponent_pitcher_hand == "L":
        return "R"
    return None


def fetch_batter_statcast_data(
    batter_id: int,
    season: int,
    batter_hand: str | None = None,
    opponent_pitcher_hand: str | None = None,
    end_date: str | None = None,
) -> Any:
    if pd is None:
        print(f"[WARN] pandas unavailable; cannot process batter Statcast data: {PANDAS_IMPORT_ERROR}")
        return None
    if statcast_batter is None:
        print(f"[WARN] pybaseball unavailable; cannot fetch batter Statcast data: {PYBASEBALL_IMPORT_ERROR}")
        return pd.DataFrame(columns=STATCAST_COLUMNS)

    start_date = f"{season}-{DEFAULT_SEASON_START_MONTH_DAY}"
    end_date = end_date or datetime.now(timezone.utc).date().isoformat()
    hand_filter = normalize_batting_side(opponent_pitcher_hand)
    cache_key = (int(batter_id), start_date, end_date, hand_filter)
    if cache_key in BATTER_STATCAST_CACHE:
        return BATTER_STATCAST_CACHE[cache_key].copy()

    try:
        df = statcast_batter(start_date, end_date, int(batter_id))
    except Exception as exc:
        print(f"[WARN] Batter Statcast fetch failed for batter_id={batter_id}: {exc}")
        df = pd.DataFrame(columns=STATCAST_COLUMNS)

    df = filter_regular_season_statcast_dataframe(normalize_statcast_dataframe(df))
    if hand_filter and df is not None and not df.empty:
        df = df[df["p_throws"] == hand_filter].copy()

    BATTER_STATCAST_CACHE[cache_key] = df.copy()
    return df


def bps_component_score(value: Any, baseline: float, scale: float, higher_is_better: bool = True) -> float:
    stat = safe_float(value)
    if stat is None:
        return 50.0
    direction = 1.0 if higher_is_better else -1.0
    return clamp(50.0 + 50.0 * direction * ((stat - baseline) / scale))


def batter_pitch_reliability(pa: Any, pitches: Any) -> float:
    pa_value = safe_float(pa, 0.0) or 0.0
    pitch_value = safe_float(pitches, 0.0) or 0.0
    if pa_value > 0:
        return clamp(min(1.0, sqrt(pa_value / BPS_PA_RELIABILITY_TARGET)), 0.0, 1.0)
    if pitch_value > 0:
        return clamp(min(1.0, sqrt(pitch_value / BPS_PITCH_RELIABILITY_TARGET)), 0.0, 1.0)
    return 0.10


def classify_batter_pitch_strength(score: Any) -> str:
    value = safe_float(score)
    if value is None:
        return "major vulnerability"
    if value >= 80:
        return "elite strength"
    if value >= 65:
        return "strong advantage"
    if value >= 50:
        return "slight advantage"
    if value >= 40:
        return "weakness"
    return "major vulnerability"


def classify_reliability(reliability: Any) -> str:
    value = safe_float(reliability, 0.0) or 0.0
    if value >= 0.80:
        return "high"
    if value >= 0.50:
        return "medium"
    return "low"


def compute_batter_pitch_strength(raw_stats: dict[str, Any]) -> dict[str, Any]:
    normalized_scores = {
        "xwOBA_score": bps_component_score(raw_stats.get("xwOBA"), 0.320, 0.080, True),
        "xSLG_score": bps_component_score(raw_stats.get("xSLG"), 0.400, 0.150, True),
        "wOBA_score": bps_component_score(raw_stats.get("wOBA"), 0.320, 0.080, True),
        "HardHit_score": bps_component_score(raw_stats.get("hard_hit_percent"), 40.0, 15.0, True),
        "Whiff_score": bps_component_score(raw_stats.get("whiff_percent"), 25.0, 15.0, False),
        "K_score": bps_component_score(raw_stats.get("strikeout_percent"), 23.0, 12.0, False),
        "RV100_score": bps_component_score(raw_stats.get("rv_per_100"), 0.0, 3.0, True),
    }
    contact_score = (
        0.60 * normalized_scores["Whiff_score"]
        + 0.40 * normalized_scores["K_score"]
    )
    normalized_scores["Contact_score"] = contact_score

    reliability = batter_pitch_reliability(raw_stats.get("PA"), raw_stats.get("pitches"))
    bps = reliability * (
        0.35 * normalized_scores["xwOBA_score"]
        + 0.20 * normalized_scores["xSLG_score"]
        + 0.15 * contact_score
        + 0.12 * normalized_scores["HardHit_score"]
        + 0.10 * normalized_scores["RV100_score"]
        + 0.08 * normalized_scores["wOBA_score"]
    )
    bps = clamp(bps)

    return {
        "bps": bps,
        "strength_label": classify_batter_pitch_strength(bps),
        "reliability": reliability,
        "reliability_label": classify_reliability(reliability),
        "normalized_scores": normalized_scores,
    }


def summarize_batter_pitch_types_from_statcast(statcast_df: Any) -> list[dict[str, Any]]:
    if pd is None or statcast_df is None or statcast_df.empty:
        return []

    df = normalize_statcast_dataframe(statcast_df)
    df = df[df["pitch_type"].notna()].copy()
    if df.empty:
        return []

    strengths: list[dict[str, Any]] = []
    denominator = len(df)
    for _, group in df.groupby("pitch_type", dropna=True):
        events = [normalize_event(value) for value in group["events"].tolist()]
        descriptions = [normalize_event(value) for value in group["description"].tolist()]
        pitch_count = len(group)
        pa = sum(1 for event in events if event)
        at_bats = sum(1 for event in events if event and event not in NON_AB_EVENTS)
        hits = count_events(events, HIT_EVENTS)
        singles = count_events(events, {"single"})
        doubles = count_events(events, {"double"})
        triples = count_events(events, {"triple"})
        home_runs = count_events(events, HOME_RUN_EVENTS)
        strikeouts = count_events(events, STRIKEOUT_EVENTS)
        total_bases = singles + 2 * doubles + 3 * triples + 4 * home_runs
        swings = sum(1 for description in descriptions if description in SWING_DESCRIPTIONS)
        whiffs = sum(1 for description in descriptions if description in WHIFF_DESCRIPTIONS)
        batted_ball_group = group[group["bb_type"].notna()]
        bbe = int(len(batted_ball_group))
        hard_hit = int((batted_ball_group["launch_speed"] >= 95.0).sum()) if "launch_speed" in batted_ball_group else 0
        expected_ba_sum = batted_ball_group["estimated_ba_using_speedangle"].sum(skipna=True)
        expected_slg_sum = batted_ball_group["estimated_slg_using_speedangle"].sum(skipna=True)
        expected_woba_values = group["estimated_woba_using_speedangle"].where(
            group["estimated_woba_using_speedangle"].notna(),
            group["woba_value"],
        )
        run_value = group["delta_run_exp"].sum(skipna=True) if "delta_run_exp" in group else None

        raw_stats = {
            "pitches": pitch_count,
            "pitch_usage_percent": safe_div(pitch_count, denominator) * 100.0,
            "PA": pa,
            "AB": at_bats,
            "H": hits,
            "BBE": bbe,
            "BA": safe_div(hits, at_bats),
            "SLG": safe_div(total_bases, at_bats),
            "wOBA": safe_div(group["woba_value"].sum(skipna=True), pa),
            "xBA": safe_div(expected_ba_sum, at_bats),
            "xSLG": safe_div(expected_slg_sum, at_bats),
            "xwOBA": safe_div(expected_woba_values.sum(skipna=True), pa),
            "whiff_percent": safe_div(whiffs, swings) * 100.0,
            "strikeout_percent": safe_div(strikeouts, pa) * 100.0,
            "hard_hit_percent": safe_div(hard_hit, bbe) * 100.0,
            "run_value": run_value,
            "rv_per_100": safe_div(run_value, pitch_count) * 100.0 if run_value is not None else None,
            "swings": swings,
            "whiffs": whiffs,
            "strikeouts": strikeouts,
        }
        strength = compute_batter_pitch_strength(raw_stats)
        strengths.append(
            {
                "pitch_type": mode_value(group["pitch_type"]),
                "pitch_name": mode_value(group["pitch_name"]),
                **strength,
                "raw_stats": raw_stats,
            }
        )

    return sorted(strengths, key=lambda row: safe_float(row.get("bps"), -1.0) or -1.0, reverse=True)


def fetch_batter_pitch_type_strengths(
    batter_id: int,
    season: int,
    batter_hand: str | None = None,
    opponent_pitcher_hand: str | None = None,
    end_date: str | None = None,
) -> list[dict[str, Any]]:
    df = fetch_batter_statcast_data(batter_id, season, batter_hand, opponent_pitcher_hand, end_date)
    return summarize_batter_pitch_types_from_statcast(df)


def calculate_batter_matchup_against_pitcher(
    batter_pitch_strengths: list[dict[str, Any]],
    pitcher_pitch_usage: list[dict[str, Any]],
) -> list[dict[str, Any]]:
    batter_by_type = {row.get("pitch_type"): row for row in batter_pitch_strengths if row.get("pitch_type")}
    matchup_rows: list[dict[str, Any]] = []

    for pitch in pitcher_pitch_usage:
        pitch_type = pitch.get("pitch_type")
        batter_row = batter_by_type.get(pitch_type)
        usage_pct = safe_float(pitch.get("usage_pct"), 0.0) or 0.0
        usage_decimal = usage_pct / 100.0 if usage_pct > 1.0 else usage_pct
        batter_bps = safe_float((batter_row or {}).get("bps"))

        matchup_rows.append(
            {
                "pitch_type": pitch_type,
                "pitch_name": pitch.get("pitch_name") or (batter_row or {}).get("pitch_name"),
                "pitcher_usage_percent": usage_decimal,
                "batter_bps": batter_bps,
                "batter_strength_label": (batter_row or {}).get("strength_label"),
                "reliability": (batter_row or {}).get("reliability"),
                "preliminary_matchup_risk": batter_bps * usage_decimal if batter_bps is not None else None,
            }
        )

    return matchup_rows


def pitcher_usage_profile_for_batter(
    pitch_rows: list[dict[str, Any]],
    game_id: Any,
    pitcher_team: str | None,
    pitcher_name: str | None,
    batter_effective_hand: str | None,
) -> list[dict[str, Any]]:
    preferred_split = f"vs {batter_effective_hand}HB" if batter_effective_hand in {"R", "L"} else "overall"
    rows = [
        row
        for row in pitch_rows
        if row.get("game_id") == game_id
        and row.get("team") == pitcher_team
        and row.get("announced_starting_pitcher") == pitcher_name
        and row.get("batter_hand_split") == preferred_split
    ]
    if rows:
        return rows

    return [
        row
        for row in pitch_rows
        if row.get("game_id") == game_id
        and row.get("team") == pitcher_team
        and row.get("announced_starting_pitcher") == pitcher_name
        and row.get("batter_hand_split") == "overall"
    ]


def build_batter_entry(
    player: dict[str, Any],
    team_name: str | None,
    opponent_pitcher: dict[str, Any],
    season: int,
    end_date: str,
    pitch_rows: list[dict[str, Any]],
    game_id: Any,
) -> dict[str, Any]:
    player_id, id_reason = resolve_player_id(player.get("name"), player.get("player_id"))
    batting_side = get_player_batting_side(player_id) if player_id else None
    opponent_hand = opponent_pitcher.get("pitcher_hand")
    effective_hand = effective_batter_hand_for_pitcher(batting_side, opponent_hand)

    strengths: list[dict[str, Any]] = []
    warnings: list[str] = []
    if player_id:
        strengths = fetch_batter_pitch_type_strengths(player_id, season, batting_side, opponent_hand, end_date)
    else:
        warnings.append(id_reason or "Missing player_id.")

    if not strengths:
        warnings.append("No batter pitch-type Statcast data available.")

    usage_profile = pitcher_usage_profile_for_batter(
        pitch_rows,
        game_id,
        opponent_pitcher.get("team_name"),
        opponent_pitcher.get("name"),
        effective_hand,
    )
    matchup_rows = calculate_batter_matchup_against_pitcher(strengths, usage_profile)

    return {
        "slot": player.get("batting_order"),
        "batting_order_slot": player.get("batting_order"),
        "player_id": player_id,
        "name": player.get("name"),
        "full_name": player.get("name"),
        "team": team_name,
        "batting_side": batting_side,
        "effective_batter_hand": effective_hand,
        "opponent_starting_pitcher": opponent_pitcher.get("name"),
        "opponent_pitcher_hand": opponent_hand,
        "warnings": warnings,
        "pitch_type_strengths": strengths,
        "preliminary_matchups": matchup_rows,
    }


def pitcher_info_for_game_side(
    game: dict[str, Any],
    side: str,
    pitcher_reports: list[dict[str, Any]],
) -> dict[str, Any]:
    pitcher_name = game.get(f"{side}_expected_starting_pitcher")
    team_name = game.get(f"{side}_team")
    report = next(
        (
            item
            for item in pitcher_reports
            if item.get("game_id") == game.get("game_id")
            and item.get("team") == team_name
            and item.get("announced_starting_pitcher") == pitcher_name
        ),
        {},
    )
    pitcher_id = report.get("pitcher_id")
    if pitcher_id is None:
        pitcher_id, _ = get_pitcher_id(pitcher_name)
    return {
        "name": pitcher_name,
        "player_id": pitcher_id,
        "pitcher_hand": get_player_pitch_hand(pitcher_id),
        "team_name": team_name,
    }


def build_batter_pitch_strength_analysis_for_game(
    game: dict[str, Any],
    pitch_rows: list[dict[str, Any]],
    pitcher_reports: list[dict[str, Any]],
    season: int,
    end_date: str,
) -> dict[str, Any]:
    away_pitcher = pitcher_info_for_game_side(game, "away", pitcher_reports)
    home_pitcher = pitcher_info_for_game_side(game, "home", pitcher_reports)
    game_dt = game.get("game_datetime_utc")
    game_date = game_dt.date().isoformat() if hasattr(game_dt, "date") else str(end_date)

    analysis = {
        "game_pk": game.get("game_id"),
        "game_id": game.get("game_id"),
        "game_date": game_date,
        "game_title": f"{game.get('away_team')} @ {game.get('home_team')}",
        "away_team": {
            "team_name": game.get("away_team"),
            "starting_pitcher": away_pitcher,
            "batters": [],
        },
        "home_team": {
            "team_name": game.get("home_team"),
            "starting_pitcher": home_pitcher,
            "batters": [],
        },
    }

    for side, opponent_pitcher in [("away", home_pitcher), ("home", away_pitcher)]:
        team_key = f"{side}_team"
        lineup_players = ((game.get(f"{side}_lineup") or {}).get("players") or [])
        analysis[team_key]["batters"] = [
            build_batter_entry(
                player,
                game.get(team_key),
                opponent_pitcher,
                season,
                end_date,
                pitch_rows,
                game.get("game_id"),
            )
            for player in lineup_players
        ]

    return analysis


def build_batter_pitch_strength_analysis_for_games(
    games: list[dict[str, Any]],
    pitch_rows: list[dict[str, Any]],
    pitcher_reports: list[dict[str, Any]],
    season: int,
    end_date: str,
) -> list[dict[str, Any]]:
    return [
        build_batter_pitch_strength_analysis_for_game(game, pitch_rows, pitcher_reports, season, end_date)
        for game in games
    ]


def flatten_batter_analysis_for_csv(analysis: dict[str, Any]) -> list[dict[str, Any]]:
    rows: list[dict[str, Any]] = []
    for side_key in ["away_team", "home_team"]:
        team = analysis.get(side_key) or {}
        for batter in team.get("batters") or []:
            for strength in batter.get("pitch_type_strengths") or []:
                raw_stats = strength.get("raw_stats") or {}
                normalized = strength.get("normalized_scores") or {}
                rows.append(
                    {
                        "game_pk": analysis.get("game_pk"),
                        "game_date": analysis.get("game_date"),
                        "game_title": analysis.get("game_title"),
                        "side": side_key.replace("_team", ""),
                        "team": team.get("team_name"),
                        "slot": batter.get("slot"),
                        "batting_order_slot": batter.get("batting_order_slot"),
                        "player_id": batter.get("player_id"),
                        "name": batter.get("name"),
                        "batting_side": batter.get("batting_side"),
                        "effective_batter_hand": batter.get("effective_batter_hand"),
                        "opponent_starting_pitcher": batter.get("opponent_starting_pitcher"),
                        "opponent_pitcher_hand": batter.get("opponent_pitcher_hand"),
                        "pitch_type": strength.get("pitch_type"),
                        "pitch_name": strength.get("pitch_name"),
                        "bps": strength.get("bps"),
                        "strength_label": strength.get("strength_label"),
                        "reliability": strength.get("reliability"),
                        "reliability_label": strength.get("reliability_label"),
                        **{f"raw_{key}": value for key, value in raw_stats.items()},
                        **{f"score_{key}": value for key, value in normalized.items()},
                    }
                )
    return rows


def flatten_batter_matchups_for_csv(analysis: dict[str, Any]) -> list[dict[str, Any]]:
    rows: list[dict[str, Any]] = []
    for side_key in ["away_team", "home_team"]:
        team = analysis.get(side_key) or {}
        for batter in team.get("batters") or []:
            for matchup in batter.get("preliminary_matchups") or []:
                rows.append(
                    {
                        "game_pk": analysis.get("game_pk"),
                        "game_date": analysis.get("game_date"),
                        "game_title": analysis.get("game_title"),
                        "side": side_key.replace("_team", ""),
                        "team": team.get("team_name"),
                        "slot": batter.get("slot"),
                        "batting_order_slot": batter.get("batting_order_slot"),
                        "player_id": batter.get("player_id"),
                        "name": batter.get("name"),
                        "batting_side": batter.get("batting_side"),
                        "opponent_starting_pitcher": batter.get("opponent_starting_pitcher"),
                        "opponent_pitcher_hand": batter.get("opponent_pitcher_hand"),
                        **matchup,
                    }
                )
    return rows


def save_batter_pitch_strength_outputs(
    analyses: list[dict[str, Any]],
    output_dir: Path | None = None,
) -> list[dict[str, Path]]:
    out_dir = output_dir or (Path(__file__).resolve().parent / "data" / "batter_pitch_strengths")
    out_dir.mkdir(parents=True, exist_ok=True)
    exported: list[dict[str, Path]] = []

    for analysis in analyses:
        game_date = analysis.get("game_date") or datetime.now(timezone.utc).date().isoformat()
        game_pk = analysis.get("game_pk") or "unknown_game"
        base = out_dir / f"{game_date}_{game_pk}"
        json_path = base.with_suffix(".json")
        strengths_csv_path = out_dir / f"{game_date}_{game_pk}_strengths.csv"
        matchups_csv_path = out_dir / f"{game_date}_{game_pk}_matchups.csv"

        json_path.write_text(json.dumps(clean_json_tree(analysis), indent=2), encoding="utf-8")

        strength_rows = flatten_batter_analysis_for_csv(analysis)
        matchup_rows = flatten_batter_matchups_for_csv(analysis)
        if pd is not None:
            pd.DataFrame(strength_rows).to_csv(strengths_csv_path, index=False)
            pd.DataFrame(matchup_rows).to_csv(matchups_csv_path, index=False)
        else:
            import csv

            for csv_path, rows in [(strengths_csv_path, strength_rows), (matchups_csv_path, matchup_rows)]:
                fieldnames = sorted({key for row in rows for key in row.keys()})
                with csv_path.open("w", newline="", encoding="utf-8") as handle:
                    writer = csv.DictWriter(handle, fieldnames=fieldnames)
                    writer.writeheader()
                    writer.writerows(rows)

        exported.append(
            {
                "json": json_path,
                "strengths_csv": strengths_csv_path,
                "matchups_csv": matchups_csv_path,
            }
        )

    return exported


def save_volatility_faceoff_outputs(
    game: dict[str, Any],
    volatility_analysis: dict[str, Any],
    output_dir: Path | None = None,
) -> dict[str, Path]:
    out_dir = output_dir or (Path(__file__).resolve().parent / "data" / "volatility_faceoffs")
    out_dir.mkdir(parents=True, exist_ok=True)

    game_dt = game.get("game_datetime_utc")
    game_date = game_dt.date().isoformat() if hasattr(game_dt, "date") else datetime.now(timezone.utc).date().isoformat()
    game_pk = game.get("game_id") or "unknown_game"
    faceoffs_csv_path = out_dir / f"{game_date}_{game_pk}_faceoffs.csv"
    faceoffs_json_path = out_dir / f"{game_date}_{game_pk}_faceoffs.json"
    summary_json_path = out_dir / f"{game_date}_{game_pk}_summary.json"
    arsenal_selection_csv_path = out_dir / f"{game_date}_{game_pk}_arsenal_selection.csv"
    arsenal_matchups_csv_path = out_dir / f"{game_date}_{game_pk}_arsenal_pitch_matchups.csv"
    arsenal_batter_scores_csv_path = out_dir / f"{game_date}_{game_pk}_arsenal_batter_scores.csv"
    weighted_batter_scores_csv_path = out_dir / f"{game_date}_{game_pk}_lineup_weighted_batter_scores.csv"
    cluster_risk_csv_path = out_dir / f"{game_date}_{game_pk}_lineup_cluster_risk.csv"
    collapse_exposure_csv_path = out_dir / f"{game_date}_{game_pk}_collapse_exposure.csv"
    escape_coverage_csv_path = out_dir / f"{game_date}_{game_pk}_escape_coverage.csv"
    lineup_risk_csv_path = out_dir / f"{game_date}_{game_pk}_lineup_run_assault_risk.csv"

    faceoffs = volatility_analysis.get("faceoffs") or []
    arsenal_analysis = volatility_analysis.get("arsenal_analysis") or {}
    faceoffs_json_path.write_text(json.dumps(clean_json_tree(faceoffs), indent=2), encoding="utf-8")
    summary_payload = {
        "game_pk": game_pk,
        "game_title": f"{game.get('away_team')} @ {game.get('home_team')}",
        "team_summaries": volatility_analysis.get("team_summaries") or [],
        "raw_game_summary": volatility_analysis.get("raw_game_summary") or {},
        "arsenal_analysis": arsenal_analysis,
        "game_summary": volatility_analysis.get("game_summary") or {},
    }
    summary_json_path.write_text(json.dumps(clean_json_tree(summary_payload), indent=2), encoding="utf-8")

    def write_rows_csv(csv_path: Path, rows: list[dict[str, Any]]) -> None:
        if pd is not None:
            pd.DataFrame(clean_json_records(rows)).to_csv(csv_path, index=False)
            return

        import csv

        clean_rows = clean_json_records(rows)
        fieldnames = sorted({key for row in clean_rows for key in row.keys()})
        with csv_path.open("w", newline="", encoding="utf-8") as handle:
            writer = csv.DictWriter(handle, fieldnames=fieldnames)
            writer.writeheader()
            writer.writerows(clean_rows)

    write_rows_csv(faceoffs_csv_path, faceoffs)
    write_rows_csv(arsenal_selection_csv_path, arsenal_analysis.get("arsenal_selection") or [])
    write_rows_csv(arsenal_matchups_csv_path, arsenal_analysis.get("pitch_level_matchups") or [])
    write_rows_csv(arsenal_batter_scores_csv_path, arsenal_analysis.get("batter_scores") or [])
    write_rows_csv(weighted_batter_scores_csv_path, arsenal_analysis.get("weighted_batter_scores") or [])
    write_rows_csv(cluster_risk_csv_path, arsenal_analysis.get("cluster_risk") or [])
    write_rows_csv(collapse_exposure_csv_path, arsenal_analysis.get("collapse_exposure") or [])
    write_rows_csv(escape_coverage_csv_path, arsenal_analysis.get("escape_coverage") or [])
    write_rows_csv(lineup_risk_csv_path, arsenal_analysis.get("lineup_run_assault_risk") or [])

    return {
        "faceoffs_csv": faceoffs_csv_path,
        "faceoffs_json": faceoffs_json_path,
        "summary_json": summary_json_path,
        "arsenal_selection_csv": arsenal_selection_csv_path,
        "arsenal_pitch_matchups_csv": arsenal_matchups_csv_path,
        "arsenal_batter_scores_csv": arsenal_batter_scores_csv_path,
        "lineup_weighted_batter_scores_csv": weighted_batter_scores_csv_path,
        "lineup_cluster_risk_csv": cluster_risk_csv_path,
        "collapse_exposure_csv": collapse_exposure_csv_path,
        "escape_coverage_csv": escape_coverage_csv_path,
        "lineup_run_assault_risk_csv": lineup_risk_csv_path,
    }


def count_events(events: Any, event_set: set[str]) -> int:
    return sum(1 for event in events if normalize_event(event) in event_set)


def launch_angle_risk_score(avg_launch_angle: Any) -> float:
    angle = safe_float(avg_launch_angle)
    if angle is None:
        return float("nan")
    if 10.0 <= angle <= 28.0:
        return 0.0
    if 0.0 <= angle < 10.0 or 28.0 < angle <= 35.0:
        return 40.0
    if -10.0 <= angle < 0.0 or 35.0 < angle <= 50.0:
        return 70.0
    return 85.0


def velocity_score_for_pitch(pitch_type: str | None, avg_velocity: Any) -> float:
    pt = (pitch_type or "").upper()
    if pt in {"FF", "FA", "SI", "FC"}:
        return score_higher_is_better(avg_velocity, bad=88.0, good=97.0)
    if pt in {"SL", "ST", "SV"}:
        return score_higher_is_better(avg_velocity, bad=78.0, good=88.0)
    if pt in {"CU", "KC"}:
        return score_higher_is_better(avg_velocity, bad=72.0, good=82.0)
    if pt in {"CH", "FS", "FO"}:
        return score_higher_is_better(avg_velocity, bad=78.0, good=88.0)
    return score_higher_is_better(avg_velocity, bad=75.0, good=95.0)


def compute_damage_risk(row: dict[str, Any]) -> float:
    risk_parts = [
        1.0 - (score_lower_is_better(row.get("xSLG_allowed"), good=0.330, bad=0.600) / 100.0),
        1.0 - (score_lower_is_better(row.get("SLG_allowed"), good=0.330, bad=0.600) / 100.0),
        1.0 - (score_lower_is_better(row.get("HR_per_BBE"), good=0.020, bad=0.120) / 100.0),
        1.0 - (score_lower_is_better(row.get("XBH_per_BBE"), good=0.060, bad=0.220) / 100.0),
    ]
    usable = [value for value in risk_parts if value == value]
    if not usable:
        return 0.5
    return clamp(sum(usable) / len(usable), 0.0, 1.0)


def compute_pitch_strength_scores(row: dict[str, Any]) -> dict[str, Any]:
    run_prevention = weighted_score(
        [
            (score_lower_is_better(row.get("xwOBA_allowed"), good=0.260, bad=0.420), 0.50),
            (score_lower_is_better(row.get("wOBA_allowed"), good=0.260, bad=0.420), 0.25),
            (score_lower_is_better(row.get("xBA_allowed"), good=0.200, bad=0.330), 0.15),
            (score_lower_is_better(row.get("BA_allowed"), good=0.200, bad=0.330), 0.10),
        ]
    )
    swing_miss = weighted_score(
        [
            (score_higher_is_better(row.get("Whiff_pct"), bad=12.0, good=35.0), 0.50),
            (score_higher_is_better(row.get("PutAway_pct"), bad=5.0, good=25.0), 0.35),
            (score_higher_is_better(row.get("SO_rate"), bad=10.0, good=35.0), 0.15),
        ]
    )
    damage_control = weighted_score(
        [
            (score_lower_is_better(row.get("xSLG_allowed"), good=0.330, bad=0.600), 0.45),
            (score_lower_is_better(row.get("SLG_allowed"), good=0.330, bad=0.600), 0.25),
            (score_lower_is_better(row.get("HR_per_BBE"), good=0.020, bad=0.120), 0.20),
            (score_lower_is_better(row.get("XBH_per_BBE"), good=0.060, bad=0.220), 0.10),
        ]
    )
    contact_quality = weighted_score(
        [
            (score_lower_is_better(row.get("avg_EV_allowed"), good=86.0, bad=94.0), 0.60),
            (launch_angle_risk_score(row.get("avg_launch_angle_allowed")), 0.40),
        ]
    )
    pitch_shape = weighted_score(
        [
            (velocity_score_for_pitch(row.get("pitch_type"), row.get("avg_velocity")), 0.40),
            (score_higher_is_better(row.get("avg_spin"), bad=1700.0, good=2600.0), 0.30),
            (score_higher_is_better(row.get("avg_extension"), bad=5.0, good=7.0), 0.30),
        ]
    )

    walk_control = weighted_score(
        [
            (score_higher_is_better(row.get("Zone_pct"), bad=ZONE_PCT_BAD, good=ZONE_PCT_GOOD), 0.40),
            (score_higher_is_better(row.get("Chase_pct"), bad=CHASE_PCT_BAD, good=CHASE_PCT_GOOD), 0.30),
            (score_higher_is_better(row.get("CalledStrike_pct"), bad=CALLED_STRIKE_PCT_BAD, good=CALLED_STRIKE_PCT_GOOD), 0.20),
            (score_lower_is_better(row.get("Ball_pct"), good=BALL_PCT_GOOD, bad=BALL_PCT_BAD), 0.10),
        ]
    )

    raw_pitch_quality_score = weighted_score(
        [
            (run_prevention, PSCORE_WEIGHT_RUN_PREVENTION),
            (swing_miss, PSCORE_WEIGHT_SWING_MISS),
            (damage_control, PSCORE_WEIGHT_DAMAGE_CONTROL),
            (walk_control, PSCORE_WEIGHT_WALK_CONTROL),
            (contact_quality, PSCORE_WEIGHT_CONTACT_QUALITY),
            (pitch_shape, PSCORE_WEIGHT_PITCH_SHAPE),
        ]
    )
    reliability_factor = min(1.0, sqrt((safe_float(row.get("pitch_count"), 0.0) or 0.0) / 300.0))
    pitch_strength_score = raw_pitch_quality_score * reliability_factor if raw_pitch_quality_score == raw_pitch_quality_score else float("nan")
    damage_risk = compute_damage_risk(row)
    usage_pct = safe_float(row.get("usage_pct"), 0.0) or 0.0

    return {
        "run_prevention_score": run_prevention,
        "swing_miss_score": swing_miss,
        "damage_control_score": damage_control,
        "walk_control_score": walk_control,
        "contact_quality_score": contact_quality,
        "pitch_shape_score": pitch_shape,
        "raw_pitch_quality_score": raw_pitch_quality_score,
        "reliability_factor": reliability_factor,
        "pitch_strength_score": pitch_strength_score,
        "damage_risk": damage_risk,
        "strategic_importance": pitch_strength_score * usage_pct if pitch_strength_score == pitch_strength_score else float("nan"),
        "pitch_vulnerability": usage_pct * (100.0 - pitch_strength_score) * damage_risk if pitch_strength_score == pitch_strength_score else float("nan"),
        "Zone_pct": row.get("Zone_pct"),
        "Ball_pct": row.get("Ball_pct"),
        "Chase_pct": row.get("Chase_pct"),
        "CalledStrike_pct": row.get("CalledStrike_pct"),
    }


def classify_pitch_strength(score: Any) -> str:
    value = safe_float(score)
    if value is None:
        return "Unknown"
    if value >= 80:
        return "Elite weapon"
    if value >= 65:
        return "Strong pitch"
    if value >= 50:
        return "Average/usable pitch"
    if value >= 35:
        return "Weak/risky pitch"
    return "Major liability"


def classify_pitch_role(usage_pct: Any) -> str:
    value = safe_float(usage_pct, 0.0) or 0.0
    if value >= 35:
        return "Primary pitch"
    if value >= 20:
        return "Main secondary pitch"
    if value >= 10:
        return "Supporting pitch"
    if value >= 5:
        return "Occasional pitch"
    return "Rare pitch"


def aggregate_pitch_group(
    pitcher_name: str,
    pitcher_id: int,
    group: Any,
    pitch_count_denominator: int,
    batter_hand_split: str,
    batter_hand: str | None,
) -> dict[str, Any]:
    events = [normalize_event(value) for value in group["events"].tolist()]
    descriptions = [normalize_event(value) for value in group["description"].tolist()]
    pitch_count = len(group)
    pa_estimate = sum(1 for event in events if event)
    bbe = int(group["bb_type"].notna().sum())
    hits = count_events(events, HIT_EVENTS)
    doubles = count_events(events, {"double"})
    triples = count_events(events, {"triple"})
    home_runs = count_events(events, HOME_RUN_EVENTS)
    singles = count_events(events, {"single"})
    strikeouts = count_events(events, STRIKEOUT_EVENTS)
    walks = count_events(events, WALK_EVENTS)
    at_bats = sum(1 for event in events if event and event not in NON_AB_EVENTS)
    total_bases = singles + 2 * doubles + 3 * triples + 4 * home_runs
    swings = sum(1 for description in descriptions if description in SWING_DESCRIPTIONS)
    whiffs = sum(1 for description in descriptions if description in WHIFF_DESCRIPTIONS)
    two_strike_pitches = int((group["strikes"] == 2).sum())
    batted_ball_group = group[group["bb_type"].notna()]
    expected_ba_sum = batted_ball_group["estimated_ba_using_speedangle"].sum(skipna=True)
    expected_slg_sum = batted_ball_group["estimated_slg_using_speedangle"].sum(skipna=True)
    expected_woba_values = group["estimated_woba_using_speedangle"].where(
        group["estimated_woba_using_speedangle"].notna(),
        group["woba_value"],
    )
    expected_woba_sum = expected_woba_values.sum(skipna=True)

    balls_thrown = sum(1 for d in descriptions if d in BALL_DESCRIPTIONS)
    called_strikes = sum(1 for d in descriptions if d in CALLED_STRIKE_DESCRIPTIONS)
    intentional_balls = sum(1 for d in descriptions if d in INTENTIONAL_BALL_DESCRIPTIONS)

    zone_values = pd.to_numeric(group["zone"], errors="coerce") if pd is not None else None
    if zone_values is not None:
        in_zone_count = int(zone_values.isin(list(IN_ZONE_NUMBERS)).sum())
        out_of_zone_count = int(zone_values.isin(list(OUT_OF_ZONE_NUMBERS)).sum())
        zone_known_count = in_zone_count + out_of_zone_count
        out_of_zone_mask = zone_values.isin(list(OUT_OF_ZONE_NUMBERS))
        chase_swings = sum(
            1
            for description, is_oz in zip(descriptions, out_of_zone_mask.tolist())
            if is_oz and description in SWING_DESCRIPTIONS
        )
    else:
        in_zone_count = 0
        out_of_zone_count = 0
        zone_known_count = 0
        chase_swings = 0

    zone_pct = (safe_div(in_zone_count, zone_known_count) * 100.0) if zone_known_count > 0 else None
    ball_pct = safe_div(balls_thrown, pitch_count) * 100.0
    chase_pct = (safe_div(chase_swings, out_of_zone_count) * 100.0) if out_of_zone_count > 0 else None
    called_strike_pct = safe_div(called_strikes, pitch_count) * 100.0

    row = {
        "pitcher": pitcher_name,
        "pitcher_id": pitcher_id,
        "pitcher_hand": mode_value(group["p_throws"]),
        "pitch_type": mode_value(group["pitch_type"]),
        "pitch_name": mode_value(group["pitch_name"]),
        "batter_hand": batter_hand or "ALL",
        "batter_hand_split": batter_hand_split,
        "batter_hand_description": hand_split_label(batter_hand),
        "pitch_count": pitch_count,
        "usage_pct": safe_div(pitch_count, pitch_count_denominator) * 100.0,
        "PA_estimate": pa_estimate,
        "AB": at_bats,
        "BBE": bbe,
        "hits": hits,
        "singles": singles,
        "doubles": doubles,
        "triples": triples,
        "home_runs": home_runs,
        "strikeouts": strikeouts,
        "walks": walks,
        "swings": swings,
        "whiffs": whiffs,
        "BA_allowed": safe_div(hits, at_bats),
        "xBA_allowed": safe_div(expected_ba_sum, at_bats),
        "SLG_allowed": safe_div(total_bases, at_bats),
        "xSLG_allowed": safe_div(expected_slg_sum, at_bats),
        "wOBA_allowed": group["woba_value"].mean(),
        "xwOBA_allowed": safe_div(expected_woba_sum, pa_estimate),
        "Whiff_pct": safe_div(whiffs, swings) * 100.0,
        "PutAway_pct": safe_div(strikeouts, two_strike_pitches) * 100.0,
        "SO_rate": safe_div(strikeouts, pa_estimate) * 100.0,
        "avg_EV_allowed": batted_ball_group["launch_speed"].mean(),
        "avg_launch_angle_allowed": batted_ball_group["launch_angle"].mean(),
        "avg_velocity": group["release_speed"].mean(),
        "avg_spin": group["release_spin_rate"].mean(),
        "avg_extension": group["release_extension"].mean(),
        "HR_per_BBE": safe_div(home_runs, bbe),
        "XBH_per_BBE": safe_div(doubles + triples + home_runs, bbe),
        "balls_thrown": balls_thrown,
        "called_strikes": called_strikes,
        "in_zone_pitches": in_zone_count,
        "out_of_zone_pitches": out_of_zone_count,
        "chase_swings": chase_swings,
        "Zone_pct": zone_pct,
        "Ball_pct": ball_pct,
        "Chase_pct": chase_pct,
        "CalledStrike_pct": called_strike_pct,
    }
    row.update(compute_pitch_strength_scores(row))
    row["classification"] = classify_pitch_strength(row["pitch_strength_score"])
    row["strategic_role"] = classify_pitch_role(row["usage_pct"])
    return row


def summarize_pitcher_pitch_types_by_hand(
    pitcher_name: str,
    pitcher_id: int,
    statcast_df: Any,
) -> list[dict[str, Any]]:
    if pd is None or statcast_df is None or statcast_df.empty:
        return []

    df = normalize_statcast_dataframe(statcast_df)
    df = df[df["pitch_type"].notna()].copy()
    if df.empty:
        return []

    summaries: list[dict[str, Any]] = []
    for split_name, hand_code, _ in BATTER_HAND_SPLITS:
        split_df = df if hand_code is None else df[df["stand"] == hand_code]
        if split_df.empty:
            continue
        denominator = len(split_df)
        for _, group in split_df.groupby("pitch_type", dropna=True):
            summaries.append(aggregate_pitch_group(pitcher_name, pitcher_id, group, denominator, split_name, hand_code))

    return summaries


def select_pitch_summary(rows: list[dict[str, Any]], split: str, mode: str) -> Optional[dict[str, Any]]:
    candidates = [row for row in rows if row.get("batter_hand_split") == split]
    if not candidates:
        return None

    if mode == "best":
        return max(candidates, key=lambda row: safe_float(row.get("pitch_strength_score"), -1.0) or -1.0)

    important = [row for row in candidates if (safe_float(row.get("usage_pct"), 0.0) or 0.0) >= 5.0]
    if not important:
        important = candidates
    return max(important, key=lambda row: safe_float(row.get("pitch_vulnerability"), -1.0) or -1.0)


def summarize_pitcher_strength_findings(rows: list[dict[str, Any]]) -> dict[str, Any]:
    findings: dict[str, Any] = {}
    for split, hand_code, hand_description in BATTER_HAND_SPLITS:
        best = select_pitch_summary(rows, split, "best")
        weak = select_pitch_summary(rows, split, "weakest")
        suffix = split.replace(" ", "_").replace("vs_", "vs_").lower()
        findings[f"batter_hand_{suffix}"] = hand_code or "ALL"
        findings[f"batter_hand_description_{suffix}"] = hand_description
        findings[f"best_pitch_{suffix}"] = best.get("pitch_name") if best else None
        findings[f"best_pitch_{suffix}_type"] = best.get("pitch_type") if best else None
        findings[f"best_pitch_{suffix}_pitcher_hand"] = best.get("pitcher_hand") if best else None
        findings[f"best_pitch_{suffix}_score"] = best.get("pitch_strength_score") if best else None
        findings[f"best_pitch_{suffix}_count"] = best.get("pitch_count") if best else None
        findings[f"best_pitch_{suffix}_usage_pct"] = best.get("usage_pct") if best else None
        findings[f"weakest_important_pitch_{suffix}"] = weak.get("pitch_name") if weak else None
        findings[f"weakest_important_pitch_{suffix}_type"] = weak.get("pitch_type") if weak else None
        findings[f"weakest_important_pitch_{suffix}_pitcher_hand"] = weak.get("pitcher_hand") if weak else None
        findings[f"weakest_important_pitch_{suffix}_vulnerability"] = weak.get("pitch_vulnerability") if weak else None
        findings[f"weakest_important_pitch_{suffix}_count"] = weak.get("pitch_count") if weak else None
        findings[f"weakest_important_pitch_{suffix}_usage_pct"] = weak.get("usage_pct") if weak else None
    return findings


def build_pitch_strength_for_pitcher(
    pitcher_name: str | None,
    start_date: str,
    end_date: str,
) -> tuple[list[dict[str, Any]], dict[str, Any]]:
    if not pitcher_name or pitcher_name == "TBD":
        return [], {"status": "missing", "reason": "No announced starting pitcher."}

    pitcher_id, reason = get_pitcher_id(pitcher_name)
    if pitcher_id is None:
        return [], {"status": "missing_id", "reason": reason}

    statcast_df = fetch_pitcher_statcast_data(pitcher_id, start_date, end_date)
    if pd is None or statcast_df is None or statcast_df.empty:
        return [], {
            "status": "no_statcast_data",
            "reason": f"No Statcast rows for {pitcher_name} ({pitcher_id}) from {start_date} to {end_date}.",
            "pitcher_id": pitcher_id,
        }

    rows = summarize_pitcher_pitch_types_by_hand(pitcher_name, pitcher_id, statcast_df)
    return rows, {
        "status": "ok",
        "reason": None,
        "pitcher_id": pitcher_id,
        "statcast_pitch_count": int(len(statcast_df)),
        **summarize_pitcher_strength_findings(rows),
    }


def add_game_context_to_pitch_rows(
    game: dict[str, Any],
    team: str | None,
    opposing_team: str | None,
    pitcher_name: str | None,
    rows: list[dict[str, Any]],
) -> list[dict[str, Any]]:
    game_dt = game.get("game_datetime_utc")
    game_dt_text = game_dt.isoformat() if hasattr(game_dt, "isoformat") else game_dt
    enriched = []

    for row in rows:
        enriched.append(
            {
                "game_id": game.get("game_id"),
                "game_datetime_utc": game_dt_text,
                "game": f"{game.get('away_team')} @ {game.get('home_team')}",
                "team": team,
                "opposing_team": opposing_team,
                "announced_starting_pitcher": pitcher_name,
                **row,
            }
        )

    return enriched


def enrich_games_with_pitchers_and_lineups(games: list[dict[str, Any]]) -> list[dict[str, Any]]:
    announced_lookup = build_announced_lineups_lookup(games)
    extracted_games: list[dict[str, Any]] = []

    for game in games:
        game_id = game.get("game_id")
        away_team = game.get("away_name")
        home_team = game.get("home_name")
        live_lineups = get_game_lineups_from_live_feed(int(game_id)) if game_id else {"away": {}, "home": {}}
        announced = get_announced_lineup_names_for_game(away_team, home_team, announced_lookup)

        away_lineup = choose_lineup(
            announced.get("away_lineup_players") or [],
            announced.get("away_lineup_status"),
            announced.get("away_lineup_reason") or announced.get("reason"),
            live_lineups.get("away") or {},
        )
        home_lineup = choose_lineup(
            announced.get("home_lineup_players") or [],
            announced.get("home_lineup_status"),
            announced.get("home_lineup_reason") or announced.get("reason"),
            live_lineups.get("home") or {},
        )

        extracted_games.append(
            {
                "game_id": game_id,
                "game_datetime_utc": game.get("parsed_game_datetime_utc"),
                "status": game.get("status"),
                "away_team": away_team,
                "home_team": home_team,
                "away_expected_starting_pitcher": game.get("away_probable_pitcher") or "TBD",
                "home_expected_starting_pitcher": game.get("home_probable_pitcher") or "TBD",
                "mlb_lineup_page_matchup": announced.get("raw_matchup_header"),
                "away_lineup": away_lineup,
                "home_lineup": home_lineup,
            }
        )

    return extracted_games


def extract_expected_pitchers_and_lineups(
    lookahead_hours: int = LOOKAHEAD_HOURS,
    lookback_hours: int = LOOKBACK_HOURS,
) -> list[dict[str, Any]]:
    games = get_games_starting_within_window(lookahead_hours, lookback_hours)
    return enrich_games_with_pitchers_and_lineups(games)


def extract_expected_pitchers_and_lineups_for_date(date_str: str) -> list[dict[str, Any]]:
    games = get_games_for_date(date_str)
    return enrich_games_with_pitchers_and_lineups(games)


def compute_pitch_strength_for_games(
    games: list[dict[str, Any]],
    end_date: str,
    start_date: str | None = None,
) -> tuple[list[dict[str, Any]], list[dict[str, Any]]]:
    statcast_start = start_date or season_start_for_end_date(end_date)
    pitch_rows: list[dict[str, Any]] = []
    pitcher_reports: list[dict[str, Any]] = []

    for game in games:
        for side, opponent_side in [("away", "home"), ("home", "away")]:
            team = game.get(f"{side}_team")
            opposing_team = game.get(f"{opponent_side}_team")
            pitcher_name = game.get(f"{side}_expected_starting_pitcher")

            rows, report = build_pitch_strength_for_pitcher(pitcher_name, statcast_start, end_date)
            context = {
                "game_id": game.get("game_id"),
                "game": f"{game.get('away_team')} @ {game.get('home_team')}",
                "team": team,
                "opposing_team": opposing_team,
                "announced_starting_pitcher": pitcher_name,
                "statcast_start_date": statcast_start,
                "statcast_end_date": end_date,
                **report,
            }
            pitcher_reports.append(context)

            if rows:
                pitch_rows.extend(add_game_context_to_pitch_rows(game, team, opposing_team, pitcher_name, rows))

    return pitch_rows, pitcher_reports


def clean_json_value(value: Any) -> Any:
    if hasattr(value, "isoformat"):
        return value.isoformat()
    if hasattr(value, "item"):
        try:
            value = value.item()
        except Exception:
            pass
    if pd is not None:
        try:
            if pd.isna(value):
                return None
        except Exception:
            pass
    if isinstance(value, float) and value != value:
        return None
    return value


def clean_json_tree(value: Any) -> Any:
    if isinstance(value, dict):
        return {key: clean_json_tree(item) for key, item in value.items()}
    if isinstance(value, list):
        return [clean_json_tree(item) for item in value]
    return clean_json_value(value)


def clean_json_records(records: list[dict[str, Any]]) -> list[dict[str, Any]]:
    return [{key: clean_json_value(value) for key, value in row.items()} for row in records]


def save_pitch_strength_outputs(
    pitch_rows: list[dict[str, Any]],
    pitcher_reports: list[dict[str, Any]],
    output_dir: Path | None = None,
) -> tuple[Path, Path]:
    out_dir = output_dir or (Path(__file__).resolve().parent / "data")
    out_dir.mkdir(parents=True, exist_ok=True)

    csv_path = out_dir / "pitcher_pitch_strength_latest.csv"
    json_path = out_dir / "pitcher_pitch_strength_latest.json"

    if pd is not None:
        pd.DataFrame(pitch_rows).to_csv(csv_path, index=False)
    else:
        import csv

        fieldnames = sorted({key for row in pitch_rows for key in row.keys()})
        with csv_path.open("w", newline="", encoding="utf-8") as handle:
            writer = csv.DictWriter(handle, fieldnames=fieldnames)
            writer.writeheader()
            writer.writerows(pitch_rows)

    payload = {
        "generated_at_utc": datetime.now(timezone.utc).isoformat(),
        "score_formula": {
            "pitch_strength_score": "reliability_factor * raw_pitch_quality_score",
            "raw_pitch_quality_score": (
                "0.30*run_prevention_score + 0.20*swing_miss_score + "
                "0.20*damage_control_score + 0.10*walk_control_score + "
                "0.15*contact_quality_score + 0.05*pitch_shape_score"
            ),
            "walk_control_score": (
                "0.40*score(Zone_pct) + 0.30*score(Chase_pct) + "
                "0.20*score(CalledStrike_pct) + 0.10*score(Ball_pct, lower_is_better)"
            ),
            "reliability_factor": "min(1.0, sqrt(pitch_count / 300))",
            "strategic_importance": "pitch_strength_score * usage_pct",
            "pitch_vulnerability": "usage_pct * (100 - pitch_strength_score) * damage_risk",
        },
        "pitch_strength_rows": clean_json_records(pitch_rows),
        "pitcher_reports": clean_json_records(pitcher_reports),
    }
    json_path.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    return csv_path, json_path


def print_lineup(title: str, lineup: dict[str, Any]) -> None:
    print(title)
    print(f"  Source: {lineup.get('source')}")
    print(f"  Status: {lineup.get('status')}")
    if lineup.get("reason"):
        print(f"  Reason: {lineup['reason']}")

    players = lineup.get("players") or []
    if not players:
        print("  No lineup available.")
        return

    for idx, player in enumerate(players, start=1):
        order = player.get("batting_order") or idx
        name = player.get("name", "N/A")
        position = player.get("position", "N/A")
        player_id = player.get("player_id")
        id_text = f" | player_id={player_id}" if player_id else ""
        print(f"  {order}. {name} ({position}){id_text}")


def truncate_table_text(value: Any, width: int) -> str:
    text = "N/A" if value in (None, "") else str(value)
    if len(text) <= width:
        return text
    if width <= 3:
        return text[:width]
    return text[: width - 3] + "..."


def fmt_table_number(value: Any, digits: int = 1) -> str:
    number = safe_float(value)
    if number is None:
        return "N/A"
    return f"{number:.{digits}f}"


def print_console_table(
    headers: list[tuple[str, int]],
    rows: list[list[Any]],
) -> None:
    if not rows:
        print("  No rows available.")
        return

    header_line = " | ".join(truncate_table_text(title, width).ljust(width) for title, width in headers)
    separator = "-+-".join("-" * width for _, width in headers)
    print(f"  {header_line}")
    print(f"  {separator}")
    for row in rows:
        cells = []
        for value, (_, width) in zip(row, headers):
            cells.append(truncate_table_text(value, width).ljust(width))
        print(f"  {' | '.join(cells)}")


def pitcher_showcase_rows_for_game(
    game: dict[str, Any],
    pitch_rows: list[dict[str, Any]],
) -> list[list[Any]]:
    rows = [
        row
        for row in pitch_rows
        if row.get("game_id") == game.get("game_id")
    ]
    split_order = {"overall": 0, "vs RHB": 1, "vs LHB": 2}
    rows.sort(
        key=lambda row: (
            str(row.get("team") or ""),
            str(row.get("announced_starting_pitcher") or ""),
            split_order.get(str(row.get("batter_hand_split")), 99),
            -(safe_float(row.get("usage_pct"), 0.0) or 0.0),
        )
    )
    return [
        [
            row.get("team"),
            row.get("announced_starting_pitcher"),
            row.get("pitcher_hand"),
            row.get("batter_hand_split"),
            f"{row.get('pitch_name')} ({row.get('pitch_type')})",
            fmt_table_number(row.get("usage_pct"), 1),
            fmt_table_number(row.get("pitch_strength_score"), 1),
            fmt_table_number(row.get("reliability_factor"), 2),
            row.get("classification"),
        ]
        for row in rows
    ]


def matchup_by_pitch_type(batter: dict[str, Any]) -> dict[Any, dict[str, Any]]:
    return {
        row.get("pitch_type"): row
        for row in (batter.get("preliminary_matchups") or [])
        if row.get("pitch_type")
    }


def batter_showcase_rows_for_team(team: dict[str, Any]) -> list[list[Any]]:
    rows: list[list[Any]] = []
    batters = sorted(team.get("batters") or [], key=lambda batter: safe_float(batter.get("slot"), 99) or 99)

    for batter in batters:
        matchup_lookup = matchup_by_pitch_type(batter)
        strengths = sorted(
            batter.get("pitch_type_strengths") or [],
            key=lambda row: (
                -(safe_float(row.get("raw_stats", {}).get("pitch_usage_percent"), 0.0) or 0.0),
                str(row.get("pitch_type") or ""),
            ),
        )
        if not strengths:
            rows.append(
                [
                    batter.get("slot"),
                    batter.get("name"),
                    batter.get("batting_side"),
                    batter.get("effective_batter_hand"),
                    batter.get("opponent_starting_pitcher"),
                    "N/A",
                    "N/A",
                    "N/A",
                    "N/A",
                    "N/A",
                    "N/A",
                ]
            )
            continue

        for strength in strengths:
            raw_stats = strength.get("raw_stats") or {}
            matchup = matchup_lookup.get(strength.get("pitch_type")) or {}
            pitcher_usage = safe_float(matchup.get("pitcher_usage_percent"))
            rows.append(
                [
                    batter.get("slot"),
                    batter.get("name"),
                    batter.get("batting_side"),
                    batter.get("effective_batter_hand"),
                    batter.get("opponent_starting_pitcher"),
                    f"{strength.get('pitch_name')} ({strength.get('pitch_type')})",
                    fmt_table_number((pitcher_usage * 100.0) if pitcher_usage is not None else None, 1),
                    fmt_table_number(raw_stats.get("pitch_usage_percent"), 1),
                    fmt_table_number(strength.get("bps"), 1),
                    f"{fmt_table_number(strength.get('reliability'), 2)} {strength.get('reliability_label')}",
                    strength.get("strength_label"),
                ]
            )

    return rows


def print_game_pitch_batter_showcase_table(
    game: dict[str, Any],
    pitch_rows: list[dict[str, Any]],
    batter_analysis: dict[str, Any] | None,
) -> None:
    print("Comprehensive pitcher/batter pitch-type showcase:")
    print()
    print("Pitcher pitch profiles:")
    print_console_table(
        [
            ("Team", 16),
            ("Pitcher", 18),
            ("Hand", 4),
            ("Split", 7),
            ("Pitch", 22),
            ("Use%", 6),
            ("PScore", 6),
            ("Rel", 5),
            ("Class", 18),
        ],
        pitcher_showcase_rows_for_game(game, pitch_rows),
    )
    print()

    if not batter_analysis:
        print("Batter pitch-strength profiles:")
        print("  No batter analysis available.")
        print()
        return

    batter_headers = [
        ("Slot", 4),
        ("Batter", 18),
        ("Side", 4),
        ("Eff", 3),
        ("Opp Pitcher", 18),
        ("Pitch", 22),
        ("PUse%", 6),
        ("BUse%", 6),
        ("BPS", 5),
        ("Rel", 10),
        ("Label", 17),
    ]
    for side_key, title in [("away_team", "Away batter pitch-strength profiles"), ("home_team", "Home batter pitch-strength profiles")]:
        team = batter_analysis.get(side_key) or {}
        print(f"{title}:")
        print_console_table(batter_headers, batter_showcase_rows_for_team(team))
        print()


def lineup_slot_weight(slot: Any, lineup_slot_weights: dict[int, float] | None = None) -> float:
    weights = lineup_slot_weights or DEFAULT_LINEUP_SLOT_WEIGHTS
    slot_int = int(safe_float(slot, 9.0) or 9)
    return weights.get(slot_int, 0.85)


def data_quality_label(combined_reliability: Any) -> str:
    return classify_reliability(combined_reliability)


def classify_volatility_score(score: Any) -> str:
    value = safe_float(score, 0.0) or 0.0
    if value >= 18:
        return "critical run-assault risk"
    if value >= 12:
        return "high volatility risk"
    if value >= 7:
        return "moderate volatility risk"
    if value >= 3:
        return "low volatility risk"
    return "minimal volatility risk"


def classify_faceoff_situation(batter_bps: Any, pitcher_score: Any, pitcher_usage_percent: Any) -> str:
    bps = safe_float(batter_bps, 0.0) or 0.0
    p_score = safe_float(pitcher_score, 0.0) or 0.0
    usage = safe_float(pitcher_usage_percent, 0.0) or 0.0
    if bps >= 75 and p_score <= 35 and usage >= 20:
        return "severe batter advantage"
    if bps >= 65 and p_score <= 45 and usage >= 15:
        return "batter advantage / volatility trigger"
    if p_score >= 65 and bps <= 45:
        return "pitcher control"
    return "neutral / uncertain"


def pitcher_split_for_effective_hand(effective_hand: str | None) -> str:
    if effective_hand == "R":
        return "vs RHB"
    if effective_hand == "L":
        return "vs LHB"
    return "overall"


def select_pitcher_profile_for_batter(
    pitcher_pitch_profiles: list[dict[str, Any]],
    pitch_type: str,
    batter_effective_hand: str | None,
) -> dict[str, Any] | None:
    wanted_split = pitcher_split_for_effective_hand(batter_effective_hand)
    split_profile = next(
        (
            row
            for row in pitcher_pitch_profiles
            if row.get("pitch_type") == pitch_type and row.get("batter_hand_split") == wanted_split
        ),
        None,
    )
    if split_profile:
        return split_profile
    return next(
        (
            row
            for row in pitcher_pitch_profiles
            if row.get("pitch_type") == pitch_type and row.get("batter_hand_split") == "overall"
        ),
        None,
    )


def build_volatility_reason(row: dict[str, Any]) -> str:
    return (
        f"{row.get('pitcher_name')} uses {row.get('pitch_name')} "
        f"{fmt_table_number(row.get('pitcher_usage_percent'), 1)}% {row.get('pitcher_split_used')}. "
        f"{row.get('batter_name')} has BPS {fmt_table_number(row.get('batter_bps'), 1)} "
        f"vs {row.get('pitch_name')} with {row.get('data_quality')} data quality. "
        f"Pitcher score is {fmt_table_number(row.get('pitcher_score'), 1)} ({row.get('pitcher_class')}). "
        f"Result: {row.get('volatility_class')} / {row.get('faceoff_situation')}."
    )


def calculate_pitcher_batter_volatility_faceoffs(
    pitcher_pitch_profiles: list[dict[str, Any]],
    batter_pitch_profiles: list[dict[str, Any]],
    lineup_slot_weights: dict[int, float] | None = None,
) -> list[dict[str, Any]]:
    faceoffs: list[dict[str, Any]] = []

    for batter in batter_pitch_profiles:
        strengths = batter.get("pitch_type_strengths") or []
        for strength in strengths:
            pitch_type = strength.get("pitch_type")
            if not pitch_type:
                continue

            pitcher_profile = select_pitcher_profile_for_batter(
                pitcher_pitch_profiles,
                str(pitch_type),
                batter.get("effective_batter_hand"),
            )
            if not pitcher_profile:
                continue

            pitcher_usage_percent = safe_float(pitcher_profile.get("usage_pct"), 0.0) or 0.0
            if pitcher_usage_percent <= 0:
                continue

            batter_bps = safe_float(strength.get("bps"))
            if batter_bps is None:
                continue

            pitcher_score = safe_float(pitcher_profile.get("pitch_strength_score"), 0.0) or 0.0
            pitcher_reliability = safe_float(pitcher_profile.get("reliability_factor"), 0.10) or 0.10
            batter_reliability = safe_float(strength.get("reliability"), 0.10) or 0.10
            usage_decimal = pitcher_usage_percent / 100.0
            slot_weight = lineup_slot_weight(batter.get("slot"), lineup_slot_weights)
            pitcher_weakness = 100.0 - pitcher_score
            base_volatility = usage_decimal * (batter_bps / 100.0) * (pitcher_weakness / 100.0)
            base_volatility *= batter_reliability * pitcher_reliability * 100.0
            volatility_score = clamp(base_volatility * slot_weight)
            combined_reliability = sqrt(max(0.0, batter_reliability * pitcher_reliability))

            raw_stats = strength.get("raw_stats") or {}
            row = {
                "game_pk": batter.get("game_pk"),
                "batting_team": batter.get("team"),
                "pitching_team": pitcher_profile.get("team"),
                "pitcher_name": pitcher_profile.get("announced_starting_pitcher"),
                "pitcher_hand": pitcher_profile.get("pitcher_hand"),
                "pitcher_split_used": pitcher_profile.get("batter_hand_split"),
                "batter_name": batter.get("name"),
                "batter_side": batter.get("batting_side"),
                "batter_effective_hand": batter.get("effective_batter_hand"),
                "lineup_slot": batter.get("slot"),
                "pitch_type": pitch_type,
                "pitch_name": pitcher_profile.get("pitch_name") or strength.get("pitch_name"),
                "pitcher_usage_percent": pitcher_usage_percent,
                "pitcher_usage_decimal": usage_decimal,
                "pitcher_score": pitcher_score,
                "pitcher_reliability": pitcher_reliability,
                "pitcher_class": pitcher_profile.get("classification"),
                "batter_seen_usage_percent": raw_stats.get("pitch_usage_percent"),
                "batter_bps": batter_bps,
                "batter_reliability": batter_reliability,
                "batter_label": strength.get("strength_label"),
                "lineup_slot_weight": slot_weight,
                "combined_reliability": combined_reliability,
                "data_quality": data_quality_label(combined_reliability),
                "volatility_score": volatility_score,
                "volatility_class": classify_volatility_score(volatility_score),
                "faceoff_situation": classify_faceoff_situation(batter_bps, pitcher_score, pitcher_usage_percent),
            }
            row["volatility_reason"] = build_volatility_reason(row)
            faceoffs.append(row)

    return sorted(faceoffs, key=lambda row: safe_float(row.get("volatility_score"), 0.0) or 0.0, reverse=True)


def flatten_batters_for_faceoffs(analysis: dict[str, Any], side_key: str) -> list[dict[str, Any]]:
    game_pk = analysis.get("game_pk")
    batters = (analysis.get(side_key) or {}).get("batters") or []
    return [{**batter, "game_pk": game_pk} for batter in batters]


def pitcher_profiles_for_team(
    pitch_rows: list[dict[str, Any]],
    game_id: Any,
    pitching_team: str | None,
    pitcher_name: str | None,
) -> list[dict[str, Any]]:
    return [
        row
        for row in pitch_rows
        if row.get("game_id") == game_id
        and row.get("team") == pitching_team
        and row.get("announced_starting_pitcher") == pitcher_name
    ]


def normalize_component(value: Any, scale: float) -> float:
    return clamp((safe_float(value, 0.0) or 0.0) / scale * 100.0)


def best_consecutive_slot_cluster(batter_totals: dict[int, float], cluster_size: int) -> float:
    if not batter_totals:
        return 0.0
    best = 0.0
    for start in range(1, 10 - cluster_size + 1):
        values = [batter_totals.get(slot, 0.0) for slot in range(start, start + cluster_size)]
        best = max(best, sum(values) / cluster_size)
    return best


def classify_team_run_assault_score(score: Any) -> str:
    value = safe_float(score, 0.0) or 0.0
    if value >= 75:
        return "very high run-assault volatility"
    if value >= 65:
        return "high run-assault volatility"
    if value >= 55:
        return "moderate positive volatility"
    if value >= 45:
        return "neutral volatility"
    return "low run-assault risk"


def classify_game_volatility_score(score: Any) -> str:
    value = safe_float(score, 0.0) or 0.0
    if value >= 75:
        return "very high game volatility"
    if value >= 65:
        return "high game volatility"
    if value >= 55:
        return "moderate game volatility"
    if value >= 45:
        return "neutral"
    return "low volatility"


def classify_volatility_asymmetry(value: Any) -> str:
    score = safe_float(value, 0.0) or 0.0
    if score >= 25:
        return "highly one-sided volatility"
    if score >= 12:
        return "moderately asymmetric"
    return "balanced volatility"


def summarize_team_run_assault(faceoffs: list[dict[str, Any]]) -> list[dict[str, Any]]:
    groups: dict[tuple[Any, Any], list[dict[str, Any]]] = {}
    for row in faceoffs:
        key = (row.get("batting_team"), row.get("pitcher_name"))
        groups.setdefault(key, []).append(row)

    summaries: list[dict[str, Any]] = []
    for (batting_team, pitcher_name), rows in groups.items():
        weighted_lineup_volatility = sum(safe_float(row.get("volatility_score"), 0.0) or 0.0 for row in rows)
        batter_totals: dict[int, float] = {}
        for row in rows:
            slot = int(safe_float(row.get("lineup_slot"), 0.0) or 0)
            if slot:
                batter_totals[slot] = batter_totals.get(slot, 0.0) + (safe_float(row.get("volatility_score"), 0.0) or 0.0)

        best_3 = best_consecutive_slot_cluster(batter_totals, 3)
        best_4 = best_consecutive_slot_cluster(batter_totals, 4)
        pitch_usage_by_type: dict[str, float] = {}
        for row in rows:
            pitch_type = str(row.get("pitch_type") or "")
            pitch_usage_by_type[pitch_type] = max(
                pitch_usage_by_type.get(pitch_type, 0.0),
                safe_float(row.get("pitcher_usage_percent"), 0.0) or 0.0,
            )
        top_pitch_types = {
            pitch_type
            for pitch_type, _ in sorted(pitch_usage_by_type.items(), key=lambda item: item[1], reverse=True)[:2]
        }
        main_pitch_rows = [row for row in rows if row.get("pitch_type") in top_pitch_types]
        main_pitch_vulnerability = (
            sum(safe_float(row.get("volatility_score"), 0.0) or 0.0 for row in main_pitch_rows) / len(main_pitch_rows)
            if main_pitch_rows
            else 0.0
        )

        normalized_weighted_lineup = normalize_component(weighted_lineup_volatility, RUN_ASSAULT_WEIGHTED_LINEUP_SCALE)
        normalized_best_4 = normalize_component(best_4, RUN_ASSAULT_BEST_4_CLUSTER_SCALE)
        normalized_main_pitch = normalize_component(main_pitch_vulnerability, RUN_ASSAULT_MAIN_PITCH_SCALE)
        normalized_best_3 = normalize_component(best_3, RUN_ASSAULT_BEST_3_CLUSTER_SCALE)
        team_score = (
            0.45 * normalized_weighted_lineup
            + 0.25 * normalized_best_4
            + 0.20 * normalized_main_pitch
            + 0.10 * normalized_best_3
        )

        summaries.append(
            {
                "batting_team": batting_team,
                "opposing_pitcher": pitcher_name,
                "weighted_lineup_volatility": weighted_lineup_volatility,
                "best_3_batter_cluster": best_3,
                "best_4_batter_cluster": best_4,
                "main_pitch_vulnerability": main_pitch_vulnerability,
                "normalized_weighted_lineup_volatility": normalized_weighted_lineup,
                "normalized_best_4_batter_cluster": normalized_best_4,
                "normalized_main_pitch_vulnerability": normalized_main_pitch,
                "normalized_best_3_batter_cluster": normalized_best_3,
                "team_run_assault_score": clamp(team_score),
                "team_run_assault_class": classify_team_run_assault_score(team_score),
            }
        )

    return sorted(summaries, key=lambda row: str(row.get("batting_team") or ""))


def summarize_game_volatility(team_summaries: list[dict[str, Any]], away_team: str | None, home_team: str | None) -> dict[str, Any]:
    score_by_team = {
        item.get("batting_team"): safe_float(item.get("team_run_assault_score"), 0.0) or 0.0
        for item in team_summaries
    }
    away_score = score_by_team.get(away_team, 0.0)
    home_score = score_by_team.get(home_team, 0.0)
    average_score = (away_score + home_score) / 2.0
    two_sided_score = min(away_score, home_score)
    shock_score = max(away_score, home_score)
    asymmetry = abs(away_score - home_score)
    game_score = (
        0.45 * average_score
        + 0.35 * two_sided_score
        + 0.20 * shock_score
        - 0.15 * asymmetry
    )
    return {
        "away_team": away_team,
        "home_team": home_team,
        "away_team_volatility": away_score,
        "home_team_volatility": home_score,
        "average_score": average_score,
        "two_sided_score": two_sided_score,
        "shock_score": shock_score,
        "game_volatility_score": game_score,
        "volatility_asymmetry": asymmetry,
        "game_volatility_class": classify_game_volatility_score(game_score),
        "volatility_asymmetry_class": classify_volatility_asymmetry(asymmetry),
    }


def classify_pitch_advantage(pitch_advantage: Any) -> str:
    value = safe_float(pitch_advantage, 0.0) or 0.0
    if value >= 25:
        return "pitcher strong advantage"
    if value >= 10:
        return "pitcher advantage"
    if value <= -25:
        return "batter strong advantage"
    if value <= -10:
        return "batter advantage"
    return "neutral"


def classify_batter_arsenal_score(score: Any) -> str:
    value = safe_float(score, 0.0) or 0.0
    if value >= 20:
        return "pitcher control"
    if value >= 8:
        return "pitcher slight advantage"
    if value <= -20:
        return "batter strong advantage"
    if value <= -8:
        return "batter pressure"
    return "neutral / execution-dependent"


def classify_lineup_run_assault_risk(score: Any) -> str:
    value = safe_float(score, 0.0) or 0.0
    if value >= 75:
        return "very high run-assault risk"
    if value >= 60:
        return "high run-assault risk"
    if value >= 45:
        return "moderate run-assault risk"
    if value >= 25:
        return "moderate-low run-assault risk"
    return "low run-assault risk"


def interpret_game_run_assault(summary: dict[str, Any]) -> str:
    away_risk = safe_float(summary.get("away_run_assault_risk"), 0.0) or 0.0
    home_risk = safe_float(summary.get("home_run_assault_risk"), 0.0) or 0.0
    two_sided = safe_float(summary.get("two_sided_volatility_score"), 0.0) or 0.0
    shock = safe_float(summary.get("one_sided_shock_score"), 0.0) or 0.0
    asymmetry = safe_float(summary.get("asymmetry"), 0.0) or 0.0
    average_score = safe_float(summary.get("average_score"), 0.0) or 0.0
    two_sided_base = safe_float(summary.get("two_sided_score"), 0.0) or 0.0

    if two_sided >= 65 and asymmetry <= 20:
        return "High two-sided volatility / good odds-crossing candidate"
    if shock >= 65 and asymmetry > 30:
        return "High one-sided shock risk / directional run-assault profile"
    if away_risk < 25 and home_risk < 25:
        return "Low run-assault environment"
    if average_score >= 45 and asymmetry > 30:
        return "Moderate volatility but one-sided profile"
    if two_sided_base < 45:
        return "Low odds-crossing potential even if one side has shock risk"
    return "Balanced arsenal-level run-assault profile"


def pitcher_split_rows_for_arsenal(
    pitcher_profiles: list[dict[str, Any]],
    split: str,
) -> list[dict[str, Any]]:
    split_rows = [row for row in pitcher_profiles if row.get("batter_hand_split") == split]
    return split_rows or [row for row in pitcher_profiles if row.get("batter_hand_split") == "overall"]


def pitcher_pitch_relevance(row: dict[str, Any]) -> float:
    usage = safe_float(row.get("usage_pct"))
    score = safe_float(row.get("pitch_strength_score"))
    reliability = safe_float(row.get("reliability_factor"))
    if usage is None or score is None or reliability is None:
        return 0.0
    return usage * score * reliability


def select_pitcher_arsenal_for_split(
    pitcher_profiles: list[dict[str, Any]],
    split: str,
) -> list[dict[str, Any]]:
    candidates = []
    for row in pitcher_split_rows_for_arsenal(pitcher_profiles, split):
        usage = safe_float(row.get("usage_pct"))
        score = safe_float(row.get("pitch_strength_score"), 50.0) or 50.0
        reliability = safe_float(row.get("reliability_factor"), 0.50) or 0.50
        relevance = pitcher_pitch_relevance(row)
        candidates.append(
            {
                "source": row,
                "usage": usage,
                "score": score,
                "reliability": reliability,
                "relevance": relevance,
            }
        )

    usable = [item for item in candidates if item["usage"] is not None and item["usage"] >= 5.0]
    if not usable:
        usable = [item for item in candidates if item["usage"] is not None]
    if not usable:
        usable = candidates[:]
    usable.sort(
        key=lambda item: (
            item["relevance"],
            safe_float(item["usage"], 0.0) or 0.0,
            item["score"] * item["reliability"],
        ),
        reverse=True,
    )

    selected_ids: set[int] = {id(item["source"]) for item in usable[:3]}
    third_relevance = usable[2]["relevance"] if len(usable) >= 3 else (usable[-1]["relevance"] if usable else 0.0)

    for item in usable[3:]:
        usage = item["usage"] or 0.0
        score = item["score"]
        relevance = item["relevance"]
        close_to_third = third_relevance > 0 and relevance >= third_relevance * 0.85
        high_usage_weak = usage >= 15.0 and score <= 40.0
        if usage >= 10.0 or close_to_third or high_usage_weak:
            selected_ids.add(id(item["source"]))
            break

    for item in usable:
        usage = item["usage"] or 0.0
        score = item["score"]
        if usage >= 22.5 or (usage >= 25.0 and score <= 40.0):
            selected_ids.add(id(item["source"]))

    top3_ids = {id(item["source"]) for item in usable[:3]}
    rows = []
    for item in sorted(candidates, key=lambda value: value["relevance"], reverse=True):
        source = item["source"]
        usage = item["usage"]
        score = item["score"]
        selected = id(source) in selected_ids
        if usage is None and selected:
            reason = "missing usage fallback"
        elif usage is None:
            reason = "missing usage excluded"
        elif not selected and usage < 5.0:
            reason = "low-usage excluded"
        elif selected and usage >= 25.0 and score <= 40.0:
            reason = "high-usage weak pitch"
        elif selected and id(source) in top3_ids:
            reason = "top relevance"
        elif selected and usage >= 22.5:
            reason = "high-usage pitch"
        elif selected:
            reason = "secondary weapon"
        else:
            reason = "outside selected arsenal"

        rows.append(
            {
                **source,
                "pitcher_name": source.get("announced_starting_pitcher"),
                "split": split,
                "pitcher_usage_pct": usage,
                "pitcher_score": score,
                "pitcher_reliability": item["reliability"],
                "pitch_relevance": item["relevance"],
                "arsenal_selected": selected,
                "selected_reason": reason,
            }
        )
    return rows


def batter_strength_for_pitch(batter: dict[str, Any], pitch_type: Any) -> tuple[dict[str, Any] | None, bool]:
    for strength in batter.get("pitch_type_strengths") or []:
        if strength.get("pitch_type") == pitch_type:
            return strength, False
    return None, True


def selected_arsenal_for_batter(arsenal_rows: list[dict[str, Any]], pitcher_name: str | None, effective_hand: str | None) -> list[dict[str, Any]]:
    split = pitcher_split_for_effective_hand(effective_hand)
    return [
        row
        for row in arsenal_rows
        if row.get("pitcher_name") == pitcher_name
        and row.get("split") == split
        and row.get("arsenal_selected")
    ]


def build_pitch_level_arsenal_matchups(
    batting_team: str | None,
    opposing_pitcher: str | None,
    batters: list[dict[str, Any]],
    arsenal_rows: list[dict[str, Any]],
) -> list[dict[str, Any]]:
    rows: list[dict[str, Any]] = []
    for batter in batters:
        effective_hand = batter.get("effective_batter_hand")
        selected = selected_arsenal_for_batter(arsenal_rows, opposing_pitcher, effective_hand)
        total_usage = sum(safe_float(row.get("pitcher_usage_pct"), 0.0) or 0.0 for row in selected)
        equal_weight = 1.0 / len(selected) if selected else 0.0

        for arsenal_pitch in selected:
            pitch_type = arsenal_pitch.get("pitch_type")
            strength, bps_fallback = batter_strength_for_pitch(batter, pitch_type)
            bps = safe_float((strength or {}).get("bps"), 50.0) or 50.0
            batter_reliability = safe_float((strength or {}).get("reliability"), 0.25) or 0.25
            pitcher_score = safe_float(arsenal_pitch.get("pitcher_score"), 50.0) or 50.0
            pitcher_reliability = safe_float(arsenal_pitch.get("pitcher_reliability"))
            pitcher_reliability_fallback = pitcher_reliability is None
            if pitcher_reliability is None:
                pitcher_reliability = 0.50
            usage_pct = safe_float(arsenal_pitch.get("pitcher_usage_pct"), 0.0) or 0.0
            usage_weight = usage_pct / total_usage if total_usage > 0 else equal_weight
            combined_reliability = sqrt(max(0.0, pitcher_reliability * batter_reliability))
            pitch_advantage = pitcher_score - bps
            bounded_advantage = max(-50.0, min(50.0, pitch_advantage))
            weighted_reliable_advantage = bounded_advantage * usage_weight * combined_reliability

            rows.append(
                {
                    "batting_team": batting_team,
                    "batter": batter.get("name"),
                    "slot": batter.get("slot"),
                    "side": batter.get("batting_side"),
                    "effective_side": effective_hand,
                    "pitcher": opposing_pitcher,
                    "pitch_type": pitch_type,
                    "pitch_name": arsenal_pitch.get("pitch_name") or (strength or {}).get("pitch_name"),
                    "pitcher_usage_pct": usage_pct,
                    "usage_weight": usage_weight,
                    "pitcher_score": pitcher_score,
                    "batter_bps": bps,
                    "pitch_advantage": pitch_advantage,
                    "pitcher_reliability": pitcher_reliability,
                    "batter_reliability": batter_reliability,
                    "combined_reliability": combined_reliability,
                    "weighted_reliable_advantage": weighted_reliable_advantage,
                    "pitch_result": classify_pitch_advantage(pitch_advantage),
                    "bps_fallback": bps_fallback,
                    "pitcher_reliability_fallback": pitcher_reliability_fallback,
                }
            )
    return rows


def consolidate_batter_arsenal_scores(pitch_matchup_rows: list[dict[str, Any]]) -> list[dict[str, Any]]:
    grouped: dict[tuple[Any, Any, Any], list[dict[str, Any]]] = {}
    for row in pitch_matchup_rows:
        key = (row.get("batting_team"), row.get("pitcher"), row.get("batter"))
        grouped.setdefault(key, []).append(row)

    results: list[dict[str, Any]] = []
    for (batting_team, pitcher, batter), rows in grouped.items():
        rows = sorted(rows, key=lambda row: safe_float(row.get("usage_weight"), 0.0) or 0.0, reverse=True)
        selected_count = len(rows)
        positive_count = sum(1 for row in rows if (safe_float(row.get("pitch_advantage"), 0.0) or 0.0) > 0)
        coverage = positive_count / selected_count if selected_count else 0.0
        escape_row = max(rows, key=lambda row: safe_float(row.get("pitch_advantage"), -999.0) or -999.0)
        danger_row = min(rows, key=lambda row: safe_float(row.get("pitch_advantage"), 999.0) or 999.0)
        escape_advantage = safe_float(escape_row.get("pitch_advantage"), 0.0) or 0.0
        danger_advantage = safe_float(danger_row.get("pitch_advantage"), 0.0) or 0.0
        batter_arsenal_score = sum(safe_float(row.get("weighted_reliable_advantage"), 0.0) or 0.0 for row in rows)
        coverage_bonus = 10.0 * (coverage - 0.5)
        escape_pitch_bonus = 0.15 * max(0.0, escape_advantage)
        danger_pitch_penalty = 0.10 * min(0.0, danger_advantage)
        final_batter_score = batter_arsenal_score + coverage_bonus + escape_pitch_bonus + danger_pitch_penalty

        results.append(
            {
                "batting_team": batting_team,
                "batter": batter,
                "slot": rows[0].get("slot"),
                "effective_side": rows[0].get("effective_side"),
                "pitcher": pitcher,
                "selected_pitches": ", ".join(str(row.get("pitch_name") or row.get("pitch_type")) for row in rows),
                "batter_arsenal_score": batter_arsenal_score,
                "coverage": coverage,
                "coverage_bonus": coverage_bonus,
                "escape_pitch": escape_row.get("pitch_name") or escape_row.get("pitch_type"),
                "escape_pitch_advantage": escape_advantage,
                "escape_pitch_bonus": escape_pitch_bonus,
                "danger_pitch": danger_row.get("pitch_name") or danger_row.get("pitch_type"),
                "danger_pitch_advantage": danger_advantage,
                "danger_pitch_penalty": danger_pitch_penalty,
                "final_batter_score": final_batter_score,
                "batter_matchup_class": classify_batter_arsenal_score(final_batter_score),
            }
        )

    return sorted(results, key=lambda row: (str(row.get("batting_team") or ""), safe_float(row.get("slot"), 99.0) or 99.0))


def build_weighted_batter_scores(batter_score_rows: list[dict[str, Any]]) -> list[dict[str, Any]]:
    rows = []
    for row in batter_score_rows:
        slot_weight = lineup_slot_weight(row.get("slot"))
        final_score = safe_float(row.get("final_batter_score"), 0.0) or 0.0
        rows.append(
            {
                "batting_team": row.get("batting_team"),
                "batter": row.get("batter"),
                "slot": row.get("slot"),
                "slot_weight": slot_weight,
                "final_batter_score": final_score,
                "weighted_batter_score": final_score * slot_weight,
                "batter_matchup_class": row.get("batter_matchup_class"),
            }
        )
    return rows


def summarize_pitcher_lineup_control(weighted_rows: list[dict[str, Any]], batter_score_rows: list[dict[str, Any]]) -> list[dict[str, Any]]:
    pitcher_by_team = {row.get("batting_team"): row.get("pitcher") for row in batter_score_rows}
    grouped: dict[Any, list[dict[str, Any]]] = {}
    for row in weighted_rows:
        grouped.setdefault(row.get("batting_team"), []).append(row)

    summaries = []
    for batting_team, rows in grouped.items():
        weight_total = sum(safe_float(row.get("slot_weight"), 0.0) or 0.0 for row in rows)
        weighted_total = sum(safe_float(row.get("weighted_batter_score"), 0.0) or 0.0 for row in rows)
        pitcher_control_score = weighted_total / weight_total if weight_total else 0.0
        summaries.append(
            {
                "batting_team": batting_team,
                "opposing_pitcher": pitcher_by_team.get(batting_team),
                "pitcher_control_score": pitcher_control_score,
                "lineup_pressure": -pitcher_control_score,
            }
        )
    return sorted(summaries, key=lambda row: str(row.get("batting_team") or ""))


def best_pressure_cluster(rows: list[dict[str, Any]], cluster_size: int) -> tuple[float, str, str]:
    by_slot = {int(safe_float(row.get("slot"), 0.0) or 0): row for row in rows}
    best_average = 0.0
    best_slots: list[int] = []
    best_batters: list[str] = []
    for start in range(1, 10 - cluster_size + 1):
        slots = list(range(start, start + cluster_size))
        cluster_rows = [by_slot.get(slot) for slot in slots]
        if any(row is None for row in cluster_rows):
            continue
        pressures = [max(0.0, -(safe_float(row.get("final_batter_score"), 0.0) or 0.0)) for row in cluster_rows if row]
        average = sum(pressures) / cluster_size if pressures else 0.0
        if average > best_average:
            best_average = average
            best_slots = slots
            best_batters = [str(row.get("batter") or "") for row in cluster_rows if row]
    return best_average, ",".join(str(slot) for slot in best_slots), ", ".join(best_batters)


def summarize_lineup_cluster_risk(batter_score_rows: list[dict[str, Any]]) -> list[dict[str, Any]]:
    grouped: dict[tuple[Any, Any], list[dict[str, Any]]] = {}
    for row in batter_score_rows:
        grouped.setdefault((row.get("batting_team"), row.get("pitcher")), []).append(row)

    summaries = []
    for (batting_team, pitcher), rows in grouped.items():
        rows = sorted(rows, key=lambda row: safe_float(row.get("slot"), 99.0) or 99.0)
        top3, top3_slots, top3_batters = best_pressure_cluster(rows, 3)
        top4, top4_slots, top4_batters = best_pressure_cluster(rows, 4)
        summaries.append(
            {
                "batting_team": batting_team,
                "opposing_pitcher": pitcher,
                "top3_cluster_pressure": top3,
                "top3_slots": top3_slots,
                "top3_batters": top3_batters,
                "top4_cluster_pressure": top4,
                "top4_slots": top4_slots,
                "top4_batters": top4_batters,
            }
        )
    return sorted(summaries, key=lambda row: str(row.get("batting_team") or ""))


def summarize_collapse_exposure(
    batter_score_rows: list[dict[str, Any]],
    pitch_matchup_rows: list[dict[str, Any]],
) -> list[dict[str, Any]]:
    grouped: dict[tuple[Any, Any], list[dict[str, Any]]] = {}
    for row in batter_score_rows:
        grouped.setdefault((row.get("batting_team"), row.get("pitcher")), []).append(row)

    exposure_rows = []
    for (batting_team, pitcher), rows in grouped.items():
        strong_count = sum(1 for row in rows if (safe_float(row.get("final_batter_score"), 0.0) or 0.0) <= -15.0)
        low_coverage_count = sum(1 for row in rows if (safe_float(row.get("coverage"), 0.0) or 0.0) <= 0.33)
        no_escape_count = sum(1 for row in rows if (safe_float(row.get("escape_pitch_advantage"), 0.0) or 0.0) <= 0.0)
        severe_danger_count = sum(1 for row in rows if (safe_float(row.get("danger_pitch_advantage"), 0.0) or 0.0) <= -30.0)
        weak_exposure = sum(
            1
            for row in pitch_matchup_rows
            if row.get("batting_team") == batting_team
            and row.get("pitcher") == pitcher
            and (safe_float(row.get("pitcher_usage_pct"), 0.0) or 0.0) >= 25.0
            and (safe_float(row.get("pitcher_score"), 100.0) or 100.0) <= 40.0
            and (safe_float(row.get("pitch_advantage"), 0.0) or 0.0) <= -10.0
        )
        raw_exposure = (
            4.0 * strong_count
            + 2.5 * low_coverage_count
            + 2.5 * no_escape_count
            + 2.0 * severe_danger_count
            + 1.5 * weak_exposure
        )
        exposure_rows.append(
            {
                "batting_team": batting_team,
                "opposing_pitcher": pitcher,
                "strong_batter_pressure_count": strong_count,
                "low_coverage_count": low_coverage_count,
                "no_escape_pitch_count": no_escape_count,
                "severe_danger_pitch_count": severe_danger_count,
                "weak_high_usage_pitch_exposure": weak_exposure,
                "raw_collapse_exposure": raw_exposure,
                "collapse_exposure": clamp(raw_exposure),
            }
        )
    return sorted(exposure_rows, key=lambda row: str(row.get("batting_team") or ""))


def summarize_escape_coverage(batter_score_rows: list[dict[str, Any]]) -> list[dict[str, Any]]:
    grouped: dict[tuple[Any, Any], list[dict[str, Any]]] = {}
    for row in batter_score_rows:
        grouped.setdefault((row.get("batting_team"), row.get("pitcher")), []).append(row)

    summaries = []
    for (batting_team, pitcher), rows in grouped.items():
        total = len(rows)
        with_escape = sum(1 for row in rows if (safe_float(row.get("escape_pitch_advantage"), 0.0) or 0.0) >= 25.0)
        score = (with_escape / total * 100.0) if total else 0.0
        summaries.append(
            {
                "batting_team": batting_team,
                "opposing_pitcher": pitcher,
                "batters_with_escape_pitch": with_escape,
                "total_batters": total,
                "escape_coverage_score": score,
            }
        )
    return sorted(summaries, key=lambda row: str(row.get("batting_team") or ""))


def summarize_lineup_run_assault_risk(
    control_rows: list[dict[str, Any]],
    cluster_rows: list[dict[str, Any]],
    collapse_rows: list[dict[str, Any]],
    escape_rows: list[dict[str, Any]],
) -> list[dict[str, Any]]:
    cluster_by_team = {row.get("batting_team"): row for row in cluster_rows}
    collapse_by_team = {row.get("batting_team"): row for row in collapse_rows}
    escape_by_team = {row.get("batting_team"): row for row in escape_rows}
    summaries = []
    for control in control_rows:
        batting_team = control.get("batting_team")
        cluster = cluster_by_team.get(batting_team) or {}
        collapse = collapse_by_team.get(batting_team) or {}
        escape = escape_by_team.get(batting_team) or {}
        lineup_pressure = safe_float(control.get("lineup_pressure"), 0.0) or 0.0
        top3 = safe_float(cluster.get("top3_cluster_pressure"), 0.0) or 0.0
        top4 = safe_float(cluster.get("top4_cluster_pressure"), 0.0) or 0.0
        collapse_exposure = safe_float(collapse.get("collapse_exposure"), 0.0) or 0.0
        escape_coverage = safe_float(escape.get("escape_coverage_score"), 0.0) or 0.0
        raw = 50.0 + 0.45 * lineup_pressure + 0.25 * top3 + 0.15 * top4 + 0.20 * collapse_exposure - 0.10 * escape_coverage
        risk = clamp(raw)
        summaries.append(
            {
                "batting_team": batting_team,
                "opposing_pitcher": control.get("opposing_pitcher"),
                "pitcher_control_score": control.get("pitcher_control_score"),
                "lineup_pressure": lineup_pressure,
                "top3_cluster_pressure": top3,
                "top4_cluster_pressure": top4,
                "collapse_exposure": collapse_exposure,
                "escape_coverage_score": escape_coverage,
                "run_assault_risk_raw": raw,
                "run_assault_risk": risk,
                "risk_class": classify_lineup_run_assault_risk(risk),
            }
        )
    return sorted(summaries, key=lambda row: str(row.get("batting_team") or ""))


def summarize_arsenal_game_run_assault(
    lineup_risk_rows: list[dict[str, Any]],
    away_team: str | None,
    home_team: str | None,
) -> dict[str, Any]:
    risk_by_team = {row.get("batting_team"): safe_float(row.get("run_assault_risk"), 0.0) or 0.0 for row in lineup_risk_rows}
    away_risk = risk_by_team.get(away_team, 0.0)
    home_risk = risk_by_team.get(home_team, 0.0)
    average_score = (away_risk + home_risk) / 2.0
    two_sided_score = min(away_risk, home_risk)
    shock_score = max(away_risk, home_risk)
    asymmetry = abs(away_risk - home_risk)
    two_sided_volatility_score = clamp(0.70 * two_sided_score + 0.20 * average_score - 0.25 * asymmetry)
    one_sided_shock_score = clamp(0.70 * shock_score + 0.20 * average_score + 0.10 * asymmetry)
    summary = {
        "away_team": away_team,
        "home_team": home_team,
        "away_run_assault_risk": away_risk,
        "home_run_assault_risk": home_risk,
        "average_score": average_score,
        "two_sided_score": two_sided_score,
        "shock_score": shock_score,
        "asymmetry": asymmetry,
        "two_sided_volatility_score": two_sided_volatility_score,
        "one_sided_shock_score": one_sided_shock_score,
    }
    summary["game_interpretation"] = interpret_game_run_assault(summary)
    return summary


# ---------------------------------------------------------------------------
# Half-Inning Volatility Analysis
#
# A half-inning only involves part of the lineup, depending on which slot leads
# off.  Instead of one team-average number, every rolling 5-batter segment (with
# wraparound past slot 9) is scored on two independent components:
#   * extension_risk      -> will the half-inning run past 3 PA (base traffic)?
#   * run_conversion_risk -> will that traffic actually become runs?
# plus a combined half-inning volatility score.  Extension and conversion stay
# numerically distinct: extension is driven by batter_pressure/contact, while
# conversion is driven by a real damage aggregate (xSLG/SLG/ISO/HardHit/xwOBA).
# ---------------------------------------------------------------------------

_HALF_INNING_WARNINGS_EMITTED: set[str] = set()


def half_inning_warn_once(message: str) -> None:
    if message not in _HALF_INNING_WARNINGS_EMITTED:
        _HALF_INNING_WARNINGS_EMITTED.add(message)
        print(message)


def _half_inning_avg(values: list[float]) -> float:
    usable = [v for v in values if v is not None]
    return sum(usable) / len(usable) if usable else 0.0


def _half_inning_minmax(values: list[float]) -> list[float]:
    nums = [safe_float(v, 0.0) or 0.0 for v in values]
    if not nums:
        return []
    low = min(nums)
    high = max(nums)
    if high - low < 1e-9:
        return [0.0 for _ in nums]
    return [clamp(100.0 * (v - low) / (high - low)) for v in nums]


def build_batter_damage_contact_lookup(batter_analysis: dict[str, Any]) -> dict[tuple[Any, Any], dict[str, Any]]:
    """Build a (team, batter_name) -> damage/contact aggregate lookup from real stats.

    These come from batter_analysis (which carries rate stats), NOT from the
    consolidated batter_scores rows (which only carry the matchup score).  This is
    what keeps extension and conversion numerically independent.
    """
    lookup: dict[tuple[Any, Any], dict[str, Any]] = {}
    for side_key in ("away_team", "home_team"):
        team_info = batter_analysis.get(side_key) or {}
        team = team_info.get("team_name")
        for batter in team_info.get("batters") or []:
            name = batter.get("name")
            damage_num = damage_weight = 0.0
            contact_num = contact_weight = 0.0
            reliability_num = reliability_weight = 0.0
            for strength in batter.get("pitch_type_strengths") or []:
                raw_stats = strength.get("raw_stats") or {}
                normalized = strength.get("normalized_scores") or {}
                usage = safe_float(raw_stats.get("pitch_usage_percent"), 0.0) or 0.0
                weight = usage if usage > 0 else 1.0

                damage_parts = [
                    score
                    for score in (
                        safe_float(normalized.get("xSLG_score")),
                        safe_float(normalized.get("HardHit_score")),
                        safe_float(normalized.get("xwOBA_score")),
                    )
                    if score is not None
                ]
                slg = safe_float(raw_stats.get("SLG"))
                batting_avg = safe_float(raw_stats.get("BA"))
                if slg is not None and batting_avg is not None:
                    iso = slg - batting_avg
                    damage_parts.append(clamp(100.0 * iso / HALF_INNING_ISO_SCALE))
                if damage_parts:
                    damage_num += (sum(damage_parts) / len(damage_parts)) * weight
                    damage_weight += weight

                contact_parts = [
                    score
                    for score in (
                        safe_float(normalized.get("Contact_score")),
                        safe_float(normalized.get("K_score")),
                    )
                    if score is not None
                ]
                if contact_parts:
                    contact_num += (sum(contact_parts) / len(contact_parts)) * weight
                    contact_weight += weight

                reliability = safe_float(strength.get("reliability"))
                if reliability is not None:
                    reliability_num += reliability * weight
                    reliability_weight += weight

            lookup[(team, name)] = {
                "batter_damage_score": clamp(damage_num / damage_weight) if damage_weight else None,
                "batter_contact_score": clamp(contact_num / contact_weight) if contact_weight else None,
                "batter_reliability": (reliability_num / reliability_weight) if reliability_weight else None,
            }
    return lookup


def build_half_inning_batter_rows(
    batter_score_rows: list[dict[str, Any]],
    damage_lookup: dict[tuple[Any, Any], dict[str, Any]],
    batting_team: Any,
) -> list[dict[str, Any]]:
    """Join the section-2 damage/contact aggregates onto one team's batter_scores."""
    rows: list[dict[str, Any]] = []
    for row in batter_score_rows:
        if row.get("batting_team") != batting_team:
            continue
        score = safe_float(row.get("final_batter_score"), 0.0) or 0.0
        name = row.get("batter")
        damage = damage_lookup.get((batting_team, name)) or {}
        damage_score = damage.get("batter_damage_score")
        contact_score = damage.get("batter_contact_score")
        rows.append(
            {
                "slot": int(safe_float(row.get("slot"), 0.0) or 0),
                "name": name,
                # Sign convention verified against best_pressure_cluster.
                "batter_pressure": max(0.0, -score),
                "pitcher_control": max(0.0, score),
                "batter_damage_score": damage_score if damage_score is not None else HALF_INNING_NEUTRAL_SCORE,
                "batter_contact_score": contact_score if contact_score is not None else HALF_INNING_NEUTRAL_SCORE,
                "batter_reliability": damage.get("batter_reliability"),
            }
        )
    return rows


def get_lineup_segments(team_batter_rows: list[dict[str, Any]], segment_size: int = 5) -> list[dict[str, Any]]:
    """Return all rolling lineup segments with wraparound past slot 9.

    Start slots run 1..9: 1-2-3-4-5, 2-3-4-5-6, ... 8-9-1-2-3, 9-1-2-3-4.
    """
    by_slot = {int(safe_float(row.get("slot"), 0.0) or 0): row for row in team_batter_rows}
    ordered = [by_slot.get(slot) for slot in range(1, 10)]
    if any(row is None for row in ordered):
        return []
    segments: list[dict[str, Any]] = []
    for start_slot in range(1, 10):
        segment_slots = [((start_slot - 1 + offset) % 9) + 1 for offset in range(segment_size)]
        seg_rows = [by_slot[slot] for slot in segment_slots]
        segments.append(
            {
                "start_slot": start_slot,
                "segment_slots": "-".join(str(slot) for slot in segment_slots),
                "segment_hitters": ", ".join(str(row.get("name") or "") for row in seg_rows),
                "rows": seg_rows,
            }
        )
    return segments


def calculate_lineup_turnover_bonus(segment_slots: str) -> float:
    """0-~20 turnover bonus for segments that roll the lineup back to the top."""
    try:
        slots = [int(part) for part in str(segment_slots).split("-") if part != ""]
    except ValueError:
        return 0.0
    if not slots:
        return 0.0
    start = slots[0]
    bonus = 0.0
    if 1 in slots:
        position = slots.index(1) + 1  # 1-based position within the segment
        if position in (4, 5):
            bonus = max(bonus, HALF_INNING_TURNOVER_SLOT1_MID)
    if start in (7, 8, 9) and (1 in slots or 2 in slots):
        bonus = max(bonus, HALF_INNING_TURNOVER_BOTTOM_TO_TOP)
    return bonus


def half_inning_pa_probability(extension_risk: float, band: tuple[float, float, float, float]) -> float:
    base, divisor, low, high = band
    return clamp(base + extension_risk / divisor, low, high)


def classify_half_inning_volatility(score: Any) -> str:
    value = safe_float(score, 0.0) or 0.0
    if value >= 75:
        return "run-assault risk"
    if value >= 60:
        return "high volatility"
    if value >= 45:
        return "pressure zone"
    if value >= 30:
        return "moderate"
    return "low"


def classify_half_inning_segment_type(
    extension_risk: float,
    run_conversion_risk: float,
    start_slot: int,
    segment_slots: str,
) -> str:
    ext_high = extension_risk >= HALF_INNING_HIGH_THRESHOLD
    ext_low = extension_risk < HALF_INNING_LOW_THRESHOLD
    conv_high = run_conversion_risk >= HALF_INNING_HIGH_THRESHOLD
    conv_low = run_conversion_risk < HALF_INNING_LOW_THRESHOLD
    ext_moderate = HALF_INNING_LOW_THRESHOLD <= extension_risk < HALF_INNING_HIGH_THRESHOLD
    try:
        slots = [int(part) for part in str(segment_slots).split("-") if part != ""]
    except ValueError:
        slots = []
    reaches_top = 1 in slots or 2 in slots
    # First match wins (order per spec).
    if ext_low and conv_low:
        return "clean inning likely"
    if ext_high and conv_low:
        return "traffic without conversion"
    if conv_high and ext_moderate:
        return "damage risk"
    if ext_high and conv_high:
        return "rally risk"
    if start_slot in (7, 8, 9) and reaches_top:
        return "bottom-to-top rollover risk"
    if start_slot in (1, 2, 3) and ext_high:
        return "top-order immediate pressure"
    return "mixed"


def compute_half_inning_segments_for_team(
    team_batter_rows: list[dict[str, Any]],
    batting_team: Any,
    opposing_pitcher: Any,
    pitcher_weakness_score: float,
    segment_size: int = HALF_INNING_SEGMENT_SIZE,
) -> list[dict[str, Any]]:
    segments = get_lineup_segments(team_batter_rows, segment_size)
    if not segments:
        return []

    # One-per-run warnings for inputs that are unavailable anywhere.
    half_inning_warn_once("Warning: sprint_speed unavailable; speed_baserunning_score defaults to neutral 50.0.")
    half_inning_warn_once("Warning: GIDP unavailable; double_play_penalty defaults to 0.0.")
    half_inning_warn_once("Warning: OBP/BB% not computed; extension uses batter_pressure + contact instead.")

    # Pass 1: raw drivers per segment.
    raw: dict[str, list[float]] = {
        "pressure_next_3": [],
        "pressure_next_5": [],
        "strongest_2_pressure": [],
        "weak_out_risk": [],
        "contact": [],
        "damage_next_3": [],
        "damage_next_5": [],
        "power_after_traffic": [],
        "turnover_bonus": [],
    }
    for seg in segments:
        hitters = seg["rows"]
        pressures = [safe_float(r.get("batter_pressure"), 0.0) or 0.0 for r in hitters]
        controls = [safe_float(r.get("pitcher_control"), 0.0) or 0.0 for r in hitters]
        damages = [safe_float(r.get("batter_damage_score"), 0.0) or 0.0 for r in hitters]
        contacts = [safe_float(r.get("batter_contact_score"), 0.0) or 0.0 for r in hitters]
        slots = [int(safe_float(r.get("slot"), 0.0) or 0) for r in hitters]

        raw["pressure_next_3"].append(_half_inning_avg(pressures[:3]))
        raw["pressure_next_5"].append(_half_inning_avg(pressures[:5]))
        raw["strongest_2_pressure"].append(_half_inning_avg(sorted(pressures[:5], reverse=True)[:2]))
        raw["weak_out_risk"].append(_half_inning_avg(controls[:3]))
        raw["contact"].append(_half_inning_avg(contacts[:5]))
        raw["damage_next_3"].append(_half_inning_avg(damages[:3]))
        raw["damage_next_5"].append(_half_inning_avg(damages[:5]))

        power_after_traffic = 0.0
        for i in range(1, len(hitters)):
            boost = 1.5 if slots[i] in (3, 4, 5) else 1.0
            power_after_traffic += pressures[i - 1] * damages[i] * boost
        raw["power_after_traffic"].append(power_after_traffic)

        raw["turnover_bonus"].append(calculate_lineup_turnover_bonus(seg["segment_slots"]))

    normalized = {key: _half_inning_minmax(values) for key, values in raw.items()}

    ext_w = HALF_INNING_EXTENSION_WEIGHTS
    conv_w = HALF_INNING_CONVERSION_WEIGHTS
    vol_w = HALF_INNING_VOLATILITY_WEIGHTS

    # Pass 2: extension, conversion, P-bands.
    extension_risks: list[float] = []
    conversion_risks: list[float] = []
    p6_values: list[float] = []
    per_segment: list[dict[str, Any]] = []
    for idx, seg in enumerate(segments):
        turnover_bonus = raw["turnover_bonus"][idx]
        extension_risk = clamp(
            ext_w["pressure_next_3"] * normalized["pressure_next_3"][idx]
            + ext_w["pressure_next_5"] * normalized["pressure_next_5"][idx]
            + ext_w["strongest_2_pressure"] * normalized["strongest_2_pressure"][idx]
            + ext_w["turnover_bonus"] * turnover_bonus
            + ext_w["weak_out_risk"] * normalized["weak_out_risk"][idx]
            + HALF_INNING_EXTENSION_CONTACT_WEIGHT * normalized["contact"][idx]
            + HALF_INNING_EXTENSION_PITCHER_WEAKNESS_WEIGHT * pitcher_weakness_score
        )
        run_conversion_risk = clamp(
            conv_w["damage_next_3"] * normalized["damage_next_3"][idx]
            + conv_w["damage_next_5"] * normalized["damage_next_5"][idx]
            + conv_w["power_after_traffic"] * normalized["power_after_traffic"][idx]
            + conv_w["speed_baserunning"] * HALF_INNING_SPEED_NEUTRAL
            + conv_w["double_play_penalty"] * HALF_INNING_DOUBLE_PLAY_DEFAULT
            + HALF_INNING_CONVERSION_PITCHER_WEAKNESS_WEIGHT * pitcher_weakness_score
        )
        p_4plus = half_inning_pa_probability(extension_risk, HALF_INNING_P4_BAND)
        p_5plus = half_inning_pa_probability(extension_risk, HALF_INNING_P5_BAND)
        p_6plus = half_inning_pa_probability(extension_risk, HALF_INNING_P6_BAND)
        extension_risks.append(extension_risk)
        conversion_risks.append(run_conversion_risk)
        p6_values.append(p_6plus)
        per_segment.append(
            {
                "batting_team": batting_team,
                "opposing_pitcher": opposing_pitcher,
                "start_slot": seg["start_slot"],
                "segment_slots": seg["segment_slots"],
                "segment_hitters": seg["segment_hitters"],
                "extension_risk": extension_risk,
                "run_conversion_risk": run_conversion_risk,
                "p_4plus_pa": p_4plus,
                "p_5plus_pa": p_5plus,
                "p_6plus_pa": p_6plus,
                "lineup_turnover_bonus": turnover_bonus,
            }
        )

    # Pass 3: combined volatility (needs P_6plus normalized across the 9 segments).
    norm_p6 = _half_inning_minmax(p6_values)
    for idx, row in enumerate(per_segment):
        volatility = clamp(
            vol_w["extension_risk"] * row["extension_risk"]
            + vol_w["run_conversion_risk"] * row["run_conversion_risk"]
            + vol_w["p_6plus"] * norm_p6[idx]
            + vol_w["turnover_bonus"] * row["lineup_turnover_bonus"]
        )
        row["volatility_score"] = volatility
        row["volatility_class"] = classify_half_inning_volatility(volatility)
        row["volatility_type"] = classify_half_inning_segment_type(
            row["extension_risk"],
            row["run_conversion_risk"],
            row["start_slot"],
            row["segment_slots"],
        )
        # Burst probability: joint event that extension AND conversion materialize.
        # P5PlusPA is the extension anchor (5 batters = real scoring threat territory).
        # TurnoverBon provides a multiplicative lift when the lineup rolls over to danger.
        _p5 = safe_float(row.get("p_5plus_pa"), 0.0) or 0.0
        _conv = (safe_float(row.get("run_conversion_risk"), 0.0) or 0.0) / 100.0
        _tbon = (safe_float(row.get("lineup_turnover_bonus"), 0.0) or 0.0) / 100.0
        row["p_burst"] = clamp(_p5 * _conv * (1.0 + _tbon) * 100.0)
    return per_segment


def summarize_team_half_inning_volatility(
    batting_team: Any,
    opposing_pitcher: Any,
    segments: list[dict[str, Any]],
) -> dict[str, Any]:
    if not segments:
        return {
            "batting_team": batting_team,
            "opposing_pitcher": opposing_pitcher,
            "avg_extension_risk": 0.0,
            "avg_run_conversion_risk": 0.0,
            "avg_volatility_score": 0.0,
            "max_volatility_score": 0.0,
            "best_start_slot": None,
            "best_segment": None,
            "avg_p_5plus_pa": 0.0,
            "avg_p_6plus_pa": 0.0,
            "high_volatility_segments": 0,
            "run_assault_segments": 0,
            "p_at_least_one_burst": 0.0,
            "expected_burst_count": 0.0,
            "max_p_burst": 0.0,
        }
    best = max(segments, key=lambda row: safe_float(row.get("volatility_score"), 0.0) or 0.0)
    # Burst aggregates across all 9 segments.
    # p_at_least_one_burst uses the complement method: P(>=1 burst) = 1 - prod(1 - p_i).
    # expected_burst_count is the raw sum under a uniform slot-visit prior.
    _burst_probs = [(safe_float(row.get("p_burst"), 0.0) or 0.0) / 100.0 for row in segments]
    _p_no_burst = 1.0
    for _bp in _burst_probs:
        _p_no_burst *= (1.0 - _bp)
    return {
        "batting_team": batting_team,
        "opposing_pitcher": opposing_pitcher,
        "avg_extension_risk": _half_inning_avg([row["extension_risk"] for row in segments]),
        "avg_run_conversion_risk": _half_inning_avg([row["run_conversion_risk"] for row in segments]),
        "avg_volatility_score": _half_inning_avg([row["volatility_score"] for row in segments]),
        "max_volatility_score": best["volatility_score"],
        "best_start_slot": best["start_slot"],
        "best_segment": best["segment_slots"],
        "avg_p_5plus_pa": _half_inning_avg([row["p_5plus_pa"] for row in segments]),
        "avg_p_6plus_pa": _half_inning_avg([row["p_6plus_pa"] for row in segments]),
        "high_volatility_segments": sum(1 for row in segments if (safe_float(row.get("volatility_score"), 0.0) or 0.0) >= 60.0),
        "run_assault_segments": sum(1 for row in segments if (safe_float(row.get("volatility_score"), 0.0) or 0.0) >= 75.0),
        "p_at_least_one_burst": clamp((1.0 - _p_no_burst) * 100.0),
        "expected_burst_count": round(sum(_burst_probs), 3),
        "max_p_burst": clamp(max(_burst_probs, default=0.0) * 100.0),
    }


def classify_game_half_inning_volatility(score: Any) -> str:
    value = safe_float(score, 0.0) or 0.0
    if value >= 80:
        return "extreme run-assault"
    if value >= 65:
        return "strong two-sided"
    if value >= 50:
        return "tradable pressure"
    if value >= 35:
        return "normal"
    return "low"


def calculate_game_half_inning_volatility(
    team_summaries: list[dict[str, Any]],
    away_team: Any,
    home_team: Any,
) -> dict[str, Any]:
    by_team = {row.get("batting_team"): row for row in team_summaries}
    away = by_team.get(away_team) or {}
    home = by_team.get(home_team) or {}
    # avg_volatility_score retained for reference fields only — no longer drives game_score.
    team1_vol = safe_float(away.get("avg_volatility_score"), 0.0) or 0.0
    team2_vol = safe_float(home.get("avg_volatility_score"), 0.0) or 0.0
    # game_volatility_score is now computed from p_at_least_one_burst (joint-event probability)
    # rather than avg_volatility_score (linear average of individual potentials).
    away_burst = safe_float(away.get("p_at_least_one_burst"), 0.0) or 0.0
    home_burst = safe_float(home.get("p_at_least_one_burst"), 0.0) or 0.0
    weights = HALF_INNING_GAME_WEIGHTS
    game_score = clamp(
        weights["avg"] * ((away_burst + home_burst) / 2.0)
        + weights["min"] * min(away_burst, home_burst)
        + weights["max"] * max(away_burst, home_burst)
        + weights["asymmetry"] * abs(away_burst - home_burst)
    )
    return {
        "away_team": away_team,
        "home_team": home_team,
        "away_avg_volatility": team1_vol,
        "home_avg_volatility": team2_vol,
        "two_sided_extension": min(
            safe_float(away.get("avg_extension_risk"), 0.0) or 0.0,
            safe_float(home.get("avg_extension_risk"), 0.0) or 0.0,
        ),
        "two_sided_conversion": min(
            safe_float(away.get("avg_run_conversion_risk"), 0.0) or 0.0,
            safe_float(home.get("avg_run_conversion_risk"), 0.0) or 0.0,
        ),
        "two_sided_p6plus": min(
            safe_float(away.get("avg_p_6plus_pa"), 0.0) or 0.0,
            safe_float(home.get("avg_p_6plus_pa"), 0.0) or 0.0,
        ),
        "asymmetry": abs(away_burst - home_burst),
        "away_p_at_least_one_burst": away_burst,
        "home_p_at_least_one_burst": home_burst,
        "away_expected_burst_count": safe_float(away.get("expected_burst_count"), 0.0) or 0.0,
        "home_expected_burst_count": safe_float(home.get("expected_burst_count"), 0.0) or 0.0,
        "game_volatility_score": game_score,
        "game_volatility_class": classify_game_half_inning_volatility(game_score),
    }


def compute_two_sided_burst_magnitude(
    away_expected_burst_count: Any,
    home_expected_burst_count: Any,
    away_run_assault_risk: Any,
    home_run_assault_risk: Any,
) -> float:
    """Single per-game two-sided burst magnitude. Blends the half-inning burst
    layer (expected_burst_count) with lineup run-assault risk at the per-team
    level, then applies the same two-sided collapse as game_volatility_score
    (HALF_INNING_GAME_WEIGHTS) exactly once. Returns 0.0 when inputs are absent
    (no lineup data), matching the empty-segment convention in
    summarize_team_half_inning_volatility."""
    w = BURST_MAGNITUDE_BLEND_WEIGHT
    away_burst_100 = clamp((safe_float(away_expected_burst_count, 0.0) or 0.0) * BURST_COUNT_TO_100_SCALE)
    home_burst_100 = clamp((safe_float(home_expected_burst_count, 0.0) or 0.0) * BURST_COUNT_TO_100_SCALE)
    away_risk = safe_float(away_run_assault_risk, 0.0) or 0.0
    home_risk = safe_float(home_run_assault_risk, 0.0) or 0.0
    team_away = w * away_burst_100 + (1.0 - w) * away_risk
    team_home = w * home_burst_100 + (1.0 - w) * home_risk
    wts = HALF_INNING_GAME_WEIGHTS
    return clamp(
        wts["avg"] * ((team_away + team_home) / 2.0)
        + wts["min"] * min(team_away, team_home)
        + wts["max"] * max(team_away, team_home)
        + wts["asymmetry"] * abs(team_away - team_home)
    )


def build_arsenal_lineup_analysis_for_game(
    game: dict[str, Any],
    batter_analysis: dict[str, Any],
    away_profiles: list[dict[str, Any]],
    home_profiles: list[dict[str, Any]],
) -> dict[str, Any]:
    away_pitcher = ((batter_analysis.get("away_team") or {}).get("starting_pitcher") or {}).get("name")
    home_pitcher = ((batter_analysis.get("home_team") or {}).get("starting_pitcher") or {}).get("name")

    arsenal_rows: list[dict[str, Any]] = []
    for pitcher_profiles, pitcher_name in [(away_profiles, away_pitcher), (home_profiles, home_pitcher)]:
        for split in ["vs LHB", "vs RHB"]:
            for row in select_pitcher_arsenal_for_split(pitcher_profiles, split):
                row["pitcher_name"] = row.get("pitcher_name") or pitcher_name
                arsenal_rows.append(row)

    away_batters = flatten_batters_for_faceoffs(batter_analysis, "away_team")
    home_batters = flatten_batters_for_faceoffs(batter_analysis, "home_team")
    pitch_matchups = []
    pitch_matchups.extend(build_pitch_level_arsenal_matchups(game.get("away_team"), home_pitcher, away_batters, arsenal_rows))
    pitch_matchups.extend(build_pitch_level_arsenal_matchups(game.get("home_team"), away_pitcher, home_batters, arsenal_rows))

    batter_scores = consolidate_batter_arsenal_scores(pitch_matchups)
    weighted_scores = build_weighted_batter_scores(batter_scores)
    control_rows = summarize_pitcher_lineup_control(weighted_scores, batter_scores)
    cluster_rows = summarize_lineup_cluster_risk(batter_scores)
    collapse_rows = summarize_collapse_exposure(batter_scores, pitch_matchups)
    escape_rows = summarize_escape_coverage(batter_scores)
    lineup_risk_rows = summarize_lineup_run_assault_risk(control_rows, cluster_rows, collapse_rows, escape_rows)
    game_summary = summarize_arsenal_game_run_assault(lineup_risk_rows, game.get("away_team"), game.get("home_team"))

    # --- Half-Inning Volatility Analysis (additive layer) ---
    damage_lookup = build_batter_damage_contact_lookup(batter_analysis)
    pitcher_by_team = {row.get("batting_team"): row.get("pitcher") for row in batter_scores}
    collapse_by_team = {row.get("batting_team"): row for row in collapse_rows}
    escape_by_team = {row.get("batting_team"): row for row in escape_rows}
    away_team = game.get("away_team")
    home_team = game.get("home_team")
    half_inning_segments: dict[Any, list[dict[str, Any]]] = {}
    half_inning_team_summary: list[dict[str, Any]] = []
    for batting_team in [away_team, home_team]:
        team_rows = build_half_inning_batter_rows(batter_scores, damage_lookup, batting_team)
        opposing_pitcher = pitcher_by_team.get(batting_team)
        collapse = collapse_by_team.get(batting_team) or {}
        escape = escape_by_team.get(batting_team) or {}
        # Higher = weaker pitcher: collapse_exposure up, escape_coverage_score down.
        pitcher_weakness_score = clamp(
            0.5 * (safe_float(collapse.get("collapse_exposure"), 0.0) or 0.0)
            + 0.5 * (100.0 - (safe_float(escape.get("escape_coverage_score"), 0.0) or 0.0))
        )
        segments = compute_half_inning_segments_for_team(
            team_rows, batting_team, opposing_pitcher, pitcher_weakness_score
        )
        half_inning_segments[batting_team] = segments
        half_inning_team_summary.append(
            summarize_team_half_inning_volatility(batting_team, opposing_pitcher, segments)
        )
    half_inning_game_profile = calculate_game_half_inning_volatility(
        half_inning_team_summary, away_team, home_team
    )
    half_inning_game_profile["two_sided_burst_magnitude"] = compute_two_sided_burst_magnitude(
        half_inning_game_profile.get("away_expected_burst_count"),
        half_inning_game_profile.get("home_expected_burst_count"),
        game_summary.get("away_run_assault_risk"),
        game_summary.get("home_run_assault_risk"),
    )

    return {
        "arsenal_selection": arsenal_rows,
        "pitch_level_matchups": pitch_matchups,
        "batter_scores": batter_scores,
        "weighted_batter_scores": weighted_scores,
        "lineup_control": control_rows,
        "cluster_risk": cluster_rows,
        "collapse_exposure": collapse_rows,
        "escape_coverage": escape_rows,
        "lineup_run_assault_risk": lineup_risk_rows,
        "game_summary": game_summary,
        "half_inning_segments": half_inning_segments,
        "half_inning_team_summary": half_inning_team_summary,
        "half_inning_game_profile": half_inning_game_profile,
    }


def build_volatility_faceoff_analysis_for_game(
    game: dict[str, Any],
    pitch_rows: list[dict[str, Any]],
    batter_analysis: dict[str, Any] | None,
) -> dict[str, Any]:
    if not batter_analysis:
        return {"faceoffs": [], "team_summaries": [], "game_summary": {}, "arsenal_analysis": {}}

    away_pitcher = (batter_analysis.get("away_team") or {}).get("starting_pitcher") or {}
    home_pitcher = (batter_analysis.get("home_team") or {}).get("starting_pitcher") or {}
    away_profiles = pitcher_profiles_for_team(pitch_rows, game.get("game_id"), game.get("away_team"), away_pitcher.get("name"))
    home_profiles = pitcher_profiles_for_team(pitch_rows, game.get("game_id"), game.get("home_team"), home_pitcher.get("name"))

    faceoffs = []
    faceoffs.extend(calculate_pitcher_batter_volatility_faceoffs(home_profiles, flatten_batters_for_faceoffs(batter_analysis, "away_team")))
    faceoffs.extend(calculate_pitcher_batter_volatility_faceoffs(away_profiles, flatten_batters_for_faceoffs(batter_analysis, "home_team")))
    faceoffs = sorted(faceoffs, key=lambda row: safe_float(row.get("volatility_score"), 0.0) or 0.0, reverse=True)
    team_summaries = summarize_team_run_assault(faceoffs)
    raw_game_summary = summarize_game_volatility(team_summaries, game.get("away_team"), game.get("home_team"))
    arsenal_analysis = build_arsenal_lineup_analysis_for_game(game, batter_analysis, away_profiles, home_profiles)
    game_summary = arsenal_analysis.get("game_summary") or raw_game_summary
    return {
        "faceoffs": faceoffs,
        "team_summaries": team_summaries,
        "raw_game_summary": raw_game_summary,
        "game_summary": game_summary,
        "arsenal_analysis": arsenal_analysis,
    }


def print_volatility_faceoff_analysis(analysis: dict[str, Any]) -> None:
    arsenal = analysis.get("arsenal_analysis") or {}

    print("Pitcher Arsenal Selection by Split")
    print_console_table(
        [
            ("Pitcher", 18),
            ("Split", 7),
            ("Pitch", 20),
            ("Usage%", 7),
            ("PScore", 6),
            ("PRel", 5),
            ("PitchRel", 9),
            ("SelectedReason", 24),
        ],
        [
            [
                row.get("pitcher_name"),
                row.get("split"),
                f"{row.get('pitch_name')} ({row.get('pitch_type')})",
                fmt_table_number(row.get("pitcher_usage_pct"), 1),
                fmt_table_number(row.get("pitcher_score"), 1),
                fmt_table_number(row.get("pitcher_reliability"), 2),
                fmt_table_number(row.get("pitch_relevance"), 1),
                row.get("selected_reason"),
            ]
            for row in (arsenal.get("arsenal_selection") or [])
        ],
    )
    print()

    print("Pitch-Level Arsenal Matchups")
    print_console_table(
        [
            ("BattingTeam", 16),
            ("Batter", 18),
            ("Slot", 4),
            ("Side", 4),
            ("Eff", 4),
            ("Pitcher", 18),
            ("Pitch", 18),
            ("Use%", 6),
            ("UWeight", 7),
            ("PScore", 6),
            ("BPS", 5),
            ("Adv", 6),
            ("PRel", 5),
            ("BRel", 5),
            ("CRel", 5),
            ("WRelAdv", 8),
            ("PitchResult", 24),
        ],
        [
            [
                row.get("batting_team"),
                row.get("batter"),
                row.get("slot"),
                row.get("side"),
                row.get("effective_side"),
                row.get("pitcher"),
                f"{row.get('pitch_name')} ({row.get('pitch_type')})",
                fmt_table_number(row.get("pitcher_usage_pct"), 1),
                fmt_table_number(row.get("usage_weight"), 2),
                fmt_table_number(row.get("pitcher_score"), 1),
                fmt_table_number(row.get("batter_bps"), 1),
                fmt_table_number(row.get("pitch_advantage"), 1),
                fmt_table_number(row.get("pitcher_reliability"), 2),
                fmt_table_number(row.get("batter_reliability"), 2),
                fmt_table_number(row.get("combined_reliability"), 2),
                fmt_table_number(row.get("weighted_reliable_advantage"), 1),
                row.get("pitch_result"),
            ]
            for row in (arsenal.get("pitch_level_matchups") or [])
        ],
    )
    print()

    print("Consolidated Pitcher-vs-Batter Arsenal Scores")
    print_console_table(
        [
            ("BattingTeam", 16),
            ("Batter", 18),
            ("Slot", 4),
            ("Eff", 4),
            ("Pitcher", 18),
            ("SelectedPitches", 28),
            ("Base", 6),
            ("Cov", 5),
            ("CovBon", 6),
            ("Escape", 16),
            ("EscAdv", 6),
            ("EscBon", 6),
            ("Danger", 16),
            ("DangAdv", 7),
            ("DangPen", 7),
            ("Final", 6),
            ("Class", 30),
        ],
        [
            [
                row.get("batting_team"),
                row.get("batter"),
                row.get("slot"),
                row.get("effective_side"),
                row.get("pitcher"),
                row.get("selected_pitches"),
                fmt_table_number(row.get("batter_arsenal_score"), 1),
                fmt_table_number(row.get("coverage"), 2),
                fmt_table_number(row.get("coverage_bonus"), 1),
                row.get("escape_pitch"),
                fmt_table_number(row.get("escape_pitch_advantage"), 1),
                fmt_table_number(row.get("escape_pitch_bonus"), 1),
                row.get("danger_pitch"),
                fmt_table_number(row.get("danger_pitch_advantage"), 1),
                fmt_table_number(row.get("danger_pitch_penalty"), 1),
                fmt_table_number(row.get("final_batter_score"), 1),
                row.get("batter_matchup_class"),
            ]
            for row in (arsenal.get("batter_scores") or [])
        ],
    )
    print()

    print("Lineup Weighted Batter Scores")
    print_console_table(
        [
            ("BattingTeam", 16),
            ("Batter", 18),
            ("Slot", 4),
            ("SlotWt", 6),
            ("Final", 6),
            ("Weighted", 8),
            ("Class", 30),
        ],
        [
            [
                row.get("batting_team"),
                row.get("batter"),
                row.get("slot"),
                fmt_table_number(row.get("slot_weight"), 2),
                fmt_table_number(row.get("final_batter_score"), 1),
                fmt_table_number(row.get("weighted_batter_score"), 1),
                row.get("batter_matchup_class"),
            ]
            for row in (arsenal.get("weighted_batter_scores") or [])
        ],
    )
    print()

    print("Pitcher-vs-Lineup Control Summary")
    print_console_table(
        [
            ("BattingTeam", 16),
            ("OppPitcher", 18),
            ("Control", 8),
            ("Pressure", 8),
        ],
        [
            [
                row.get("batting_team"),
                row.get("opposing_pitcher"),
                fmt_table_number(row.get("pitcher_control_score"), 1),
                fmt_table_number(row.get("lineup_pressure"), 1),
            ]
            for row in (arsenal.get("lineup_control") or [])
        ],
    )
    print()

    print("Lineup Cluster Risk")
    print_console_table(
        [
            ("BattingTeam", 16),
            ("OppPitcher", 18),
            ("Top3", 6),
            ("Top3Slots", 9),
            ("Top3Batters", 30),
            ("Top4", 6),
            ("Top4Slots", 9),
            ("Top4Batters", 30),
        ],
        [
            [
                row.get("batting_team"),
                row.get("opposing_pitcher"),
                fmt_table_number(row.get("top3_cluster_pressure"), 1),
                row.get("top3_slots"),
                row.get("top3_batters"),
                fmt_table_number(row.get("top4_cluster_pressure"), 1),
                row.get("top4_slots"),
                row.get("top4_batters"),
            ]
            for row in (arsenal.get("cluster_risk") or [])
        ],
    )
    print()

    print("Collapse Exposure Components")
    print_console_table(
        [
            ("BattingTeam", 16),
            ("OppPitcher", 18),
            ("Strong", 6),
            ("LowCov", 6),
            ("NoEsc", 6),
            ("SevDang", 7),
            ("WeakUse", 7),
            ("Raw", 6),
        ],
        [
            [
                row.get("batting_team"),
                row.get("opposing_pitcher"),
                row.get("strong_batter_pressure_count"),
                row.get("low_coverage_count"),
                row.get("no_escape_pitch_count"),
                row.get("severe_danger_pitch_count"),
                row.get("weak_high_usage_pitch_exposure"),
                fmt_table_number(row.get("raw_collapse_exposure"), 1),
            ]
            for row in (arsenal.get("collapse_exposure") or [])
        ],
    )
    print()

    print("Escape Coverage")
    print_console_table(
        [
            ("BattingTeam", 16),
            ("OppPitcher", 18),
            ("WithEsc", 7),
            ("Total", 5),
            ("EscCov", 7),
        ],
        [
            [
                row.get("batting_team"),
                row.get("opposing_pitcher"),
                row.get("batters_with_escape_pitch"),
                row.get("total_batters"),
                fmt_table_number(row.get("escape_coverage_score"), 1),
            ]
            for row in (arsenal.get("escape_coverage") or [])
        ],
    )
    print()

    print("Lineup Run-Assault Risk Summary")
    print_console_table(
        [
            ("BattingTeam", 16),
            ("OppPitcher", 18),
            ("Control", 7),
            ("Pressure", 8),
            ("Top3", 6),
            ("Top4", 6),
            ("Collapse", 8),
            ("EscCov", 7),
            ("Raw", 6),
            ("Risk", 6),
            ("RiskClass", 30),
        ],
        [
            [
                row.get("batting_team"),
                row.get("opposing_pitcher"),
                fmt_table_number(row.get("pitcher_control_score"), 1),
                fmt_table_number(row.get("lineup_pressure"), 1),
                fmt_table_number(row.get("top3_cluster_pressure"), 1),
                fmt_table_number(row.get("top4_cluster_pressure"), 1),
                fmt_table_number(row.get("collapse_exposure"), 1),
                fmt_table_number(row.get("escape_coverage_score"), 1),
                fmt_table_number(row.get("run_assault_risk_raw"), 1),
                fmt_table_number(row.get("run_assault_risk"), 1),
                row.get("risk_class"),
            ]
            for row in (arsenal.get("lineup_run_assault_risk") or [])
        ],
    )
    print()

    print("Raw Highest Theoretical Pitch Mismatches")
    print(
        "  These are raw pitch-level mismatch opportunities. They do not necessarily represent the most likely "
        "played scenarios because they are not fully adjusted for arsenal coverage, pitch avoidability, "
        "lineup clustering, or pitcher escape options."
    )
    print_console_table(
        [
            ("Pitcher", 18),
            ("Pitch", 18),
            ("Split", 7),
            ("Batter", 18),
            ("Slot", 4),
            ("Hand", 4),
            ("Use%", 6),
            ("PScore", 6),
            ("BPS", 5),
            ("Vol", 5),
            ("Class", 24),
            ("Situation", 32),
        ],
        [
            [
                row.get("pitcher_name"),
                f"{row.get('pitch_name')} ({row.get('pitch_type')})",
                row.get("pitcher_split_used"),
                row.get("batter_name"),
                row.get("lineup_slot"),
                row.get("batter_effective_hand") or row.get("batter_side"),
                fmt_table_number(row.get("pitcher_usage_percent"), 1),
                fmt_table_number(row.get("pitcher_score"), 1),
                fmt_table_number(row.get("batter_bps"), 1),
                fmt_table_number(row.get("volatility_score"), 1),
                row.get("volatility_class"),
                row.get("faceoff_situation"),
            ]
            for row in (analysis.get("faceoffs") or [])[:15]
        ],
    )
    print()

    print("Game Run-Assault / Volatility Summary")
    game_summary = analysis.get("game_summary") or {}
    print_console_table(
        [
            ("AwayTeam", 16),
            ("HomeTeam", 16),
            ("AwayRisk", 8),
            ("HomeRisk", 8),
            ("Avg", 6),
            ("TwoSide", 7),
            ("Shock", 6),
            ("Asym", 6),
            ("TwoVol", 7),
            ("ShockSc", 7),
            ("Interpretation", 48),
        ],
        [
            [
                game_summary.get("away_team"),
                game_summary.get("home_team"),
                fmt_table_number(game_summary.get("away_run_assault_risk"), 1),
                fmt_table_number(game_summary.get("home_run_assault_risk"), 1),
                fmt_table_number(game_summary.get("average_score"), 1),
                fmt_table_number(game_summary.get("two_sided_score"), 1),
                fmt_table_number(game_summary.get("shock_score"), 1),
                fmt_table_number(game_summary.get("asymmetry"), 1),
                fmt_table_number(game_summary.get("two_sided_volatility_score"), 1),
                fmt_table_number(game_summary.get("one_sided_shock_score"), 1),
                game_summary.get("game_interpretation"),
            ]
        ] if game_summary else [],
    )
    print()

    half_inning_segments = arsenal.get("half_inning_segments") or {}
    half_inning_team_summary = arsenal.get("half_inning_team_summary") or []
    half_inning_game_profile = arsenal.get("half_inning_game_profile") or {}

    print("HALF-INNING VOLATILITY ANALYSIS")
    segment_rows: list[list[Any]] = []
    for summary in half_inning_team_summary:
        team = summary.get("batting_team")
        for seg in half_inning_segments.get(team) or []:
            segment_rows.append(
                [
                    seg.get("batting_team"),
                    seg.get("opposing_pitcher"),
                    seg.get("start_slot"),
                    seg.get("segment_hitters"),
                    seg.get("segment_slots"),
                    fmt_table_number(seg.get("extension_risk"), 1),
                    fmt_table_number(seg.get("run_conversion_risk"), 1),
                    fmt_table_number(seg.get("p_4plus_pa"), 2),
                    fmt_table_number(seg.get("p_5plus_pa"), 2),
                    fmt_table_number(seg.get("p_6plus_pa"), 2),
                    fmt_table_number(seg.get("lineup_turnover_bonus"), 1),
                    fmt_table_number(seg.get("volatility_score"), 1),
                    seg.get("volatility_class"),
                    seg.get("volatility_type"),
                ]
            )
    print_console_table(
        [
            ("BattingTeam", 16),
            ("OppPitcher", 18),
            ("StartSlot", 9),
            ("SegmentHitters", 40),
            ("SegmentSlots", 12),
            ("ExtRisk", 7),
            ("ConvRisk", 8),
            ("P4PlusPA", 8),
            ("P5PlusPA", 8),
            ("P6PlusPA", 8),
            ("TurnoverBon", 11),
            ("Volatility", 10),
            ("VolClass", 18),
            ("VolType", 28),
        ],
        segment_rows,
    )
    print()

    print("HALF-INNING VOLATILITY SUMMARY")
    print_console_table(
        [
            ("BattingTeam", 16),
            ("OppPitcher", 18),
            ("AvgExtRisk", 10),
            ("AvgConvRisk", 11),
            ("AvgVol", 7),
            ("MaxVol", 7),
            ("BestSlot", 8),
            ("BestSegment", 12),
            ("AvgP5Plus", 9),
            ("AvgP6Plus", 9),
            ("HighVol", 7),
            ("RunAssault", 10),
            ("P1Burst%", 9),
            ("ExpBursts", 9),
        ],
        [
            [
                row.get("batting_team"),
                row.get("opposing_pitcher"),
                fmt_table_number(row.get("avg_extension_risk"), 1),
                fmt_table_number(row.get("avg_run_conversion_risk"), 1),
                fmt_table_number(row.get("avg_volatility_score"), 1),
                fmt_table_number(row.get("max_volatility_score"), 1),
                row.get("best_start_slot"),
                row.get("best_segment"),
                fmt_table_number(row.get("avg_p_5plus_pa"), 2),
                fmt_table_number(row.get("avg_p_6plus_pa"), 2),
                row.get("high_volatility_segments"),
                row.get("run_assault_segments"),
                fmt_table_number(row.get("p_at_least_one_burst"), 1),
                fmt_table_number(row.get("expected_burst_count"), 2),
            ]
            for row in half_inning_team_summary
        ],
    )
    print()

    print("GAME HALF-INNING VOLATILITY PROFILE")
    print_console_table(
        [
            ("AwayTeam", 16),
            ("HomeTeam", 16),
            ("AwayBurst%", 10),
            ("HomeBurst%", 10),
            ("TwoSideExt", 10),
            ("TwoSideConv", 11),
            ("TwoSideP6", 9),
            ("Asymmetry", 9),
            ("GameVol", 7),
            ("BurstMag", 9),
            ("GameClass", 20),
        ],
        [
            [
                half_inning_game_profile.get("away_team"),
                half_inning_game_profile.get("home_team"),
                fmt_table_number(half_inning_game_profile.get("away_p_at_least_one_burst"), 1),
                fmt_table_number(half_inning_game_profile.get("home_p_at_least_one_burst"), 1),
                fmt_table_number(half_inning_game_profile.get("two_sided_extension"), 1),
                fmt_table_number(half_inning_game_profile.get("two_sided_conversion"), 1),
                fmt_table_number(half_inning_game_profile.get("two_sided_p6plus"), 2),
                fmt_table_number(half_inning_game_profile.get("asymmetry"), 1),
                fmt_table_number(half_inning_game_profile.get("game_volatility_score"), 1),
                fmt_table_number(half_inning_game_profile.get("two_sided_burst_magnitude"), 1),
                half_inning_game_profile.get("game_volatility_class"),
            ]
        ] if half_inning_game_profile else [],
    )
    print()


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description="Extract MLB announced starters, lineups, and Baseball Savant pitch-type strength."
    )
    parser.add_argument("--date", help="Game date to analyze, YYYY-MM-DD. If omitted, uses next lookahead window.")
    parser.add_argument("--start-date", help="Statcast start date, YYYY-MM-DD. Default: season start for --date/end date.")
    parser.add_argument("--lookahead-hours", type=int, default=LOOKAHEAD_HOURS)
    parser.add_argument("--lookback-hours", type=int, default=LOOKBACK_HOURS)
    return parser.parse_args()


def main() -> None:
    args = parse_args()
    now_utc = datetime.now(timezone.utc)

    if args.date:
        games = extract_expected_pitchers_and_lineups_for_date(args.date)
        statcast_end_date = args.date
        print(f"Analyzing MLB games for date: {args.date}")
    else:
        window_start_utc = now_utc - timedelta(hours=args.lookback_hours)
        window_end_utc = now_utc + timedelta(hours=args.lookahead_hours)
        games = extract_expected_pitchers_and_lineups(args.lookahead_hours, args.lookback_hours)
        statcast_end_date = now_utc.date().isoformat()
        print(f"Current UTC time: {now_utc.isoformat()}")
        print(f"Checking games starting from: {window_start_utc.isoformat()}")
        print(f"Checking games starting until: {window_end_utc.isoformat()}")

    print()

    if not games:
        if args.date:
            print(f"No MLB games found for {args.date}.")
        else:
            print(
                "No MLB games found starting "
                f"from {args.lookback_hours} hours ago through next {args.lookahead_hours} hours."
            )
        return

    pitch_rows, pitcher_reports = compute_pitch_strength_for_games(
        games,
        end_date=statcast_end_date,
        start_date=args.start_date,
    )
    csv_path, json_path = save_pitch_strength_outputs(pitch_rows, pitcher_reports)
    batter_analyses = build_batter_pitch_strength_analysis_for_games(
        games,
        pitch_rows,
        pitcher_reports,
        season=int(statcast_end_date[:4]),
        end_date=statcast_end_date,
    )
    batter_export_paths = save_batter_pitch_strength_outputs(batter_analyses)
    batter_analysis_by_game_id = {analysis.get("game_id"): analysis for analysis in batter_analyses}
    volatility_analysis_by_game_id = {
        game.get("game_id"): build_volatility_faceoff_analysis_for_game(
            game,
            pitch_rows,
            batter_analysis_by_game_id.get(game.get("game_id")),
        )
        for game in games
    }
    volatility_export_paths = [
        save_volatility_faceoff_outputs(game, volatility_analysis_by_game_id.get(game.get("game_id")) or {})
        for game in games
    ]

    for idx, game in enumerate(games, start=1):
        game_dt = game.get("game_datetime_utc")

        print("=" * 100)
        print(f"Game {idx}: {game['away_team']} @ {game['home_team']}")
        print(f"Game ID: {game['game_id']}")
        print(f"Status: {game['status']}")
        print(f"Start time UTC: {game_dt.isoformat() if game_dt else 'Unknown'}")
        print(f"MLB lineup page matchup: {game.get('mlb_lineup_page_matchup')}")
        print()

        print("Expected starting pitchers:")
        print(f"  Away: {game['away_expected_starting_pitcher']}")
        print(f"  Home: {game['home_expected_starting_pitcher']}")
        print()

        print_lineup(f"Away batting lineup: {game['away_team']}", game["away_lineup"])
        print()
        print_lineup(f"Home batting lineup: {game['home_team']}", game["home_lineup"])
        print()
        game_batter_analysis = batter_analysis_by_game_id.get(game.get("game_id"))
        print_game_pitch_batter_showcase_table(game, pitch_rows, game_batter_analysis)
        print_volatility_faceoff_analysis(volatility_analysis_by_game_id.get(game.get("game_id")) or {})

    print(f"Saved CSV: {csv_path}")
    print(f"Saved JSON: {json_path}")
    for exported in batter_export_paths:
        print(f"Saved batter JSON: {exported['json']}")
        print(f"Saved batter strengths CSV: {exported['strengths_csv']}")
        print(f"Saved batter matchups CSV: {exported['matchups_csv']}")
    for exported in volatility_export_paths:
        print(f"Saved volatility faceoffs CSV: {exported['faceoffs_csv']}")
        print(f"Saved volatility faceoffs JSON: {exported['faceoffs_json']}")
        print(f"Saved volatility summary JSON: {exported['summary_json']}")
        print(f"Saved arsenal selection CSV: {exported['arsenal_selection_csv']}")
        print(f"Saved arsenal pitch matchups CSV: {exported['arsenal_pitch_matchups_csv']}")
        print(f"Saved arsenal batter scores CSV: {exported['arsenal_batter_scores_csv']}")
        print(f"Saved lineup weighted batter scores CSV: {exported['lineup_weighted_batter_scores_csv']}")
        print(f"Saved lineup cluster risk CSV: {exported['lineup_cluster_risk_csv']}")
        print(f"Saved collapse exposure CSV: {exported['collapse_exposure_csv']}")
        print(f"Saved escape coverage CSV: {exported['escape_coverage_csv']}")
        print(f"Saved lineup run-assault risk CSV: {exported['lineup_run_assault_risk_csv']}")

    print()
    print("Half-Inning Volatility Analysis — how to read it:")
    print("  - Extension risk estimates how likely a half-inning runs past 3 PA (longer innings, more base traffic).")
    print("  - Run conversion risk estimates whether that traffic actually turns into runs (real damage stats, not pressure).")
    print("  - Half-inning volatility is highest when BOTH extension and conversion are elevated for the same segment.")
    print("  - Game volatility is highest when BOTH teams have several dangerous segments; it is penalized when one team dominates.")


if __name__ == "__main__":
    main()
