from __future__ import annotations

from datetime import datetime, timedelta, timezone
from typing import Any, Optional
import io
import re
import csv
import json
import unicodedata
from math import exp
from pathlib import Path
from zoneinfo import ZoneInfo

import requests
import statsapi
import pandas as pd
from bs4 import BeautifulSoup

from pybaseball import playerid_lookup


SEASON = 2026
LOOKAHEAD_HOURS = 10
PITCHER_FULL_SEASON_IP = 162.0  # reference IP for reliability factor (~27 starts × 6 IP)
MLB_STATS_API_BASE = "https://statsapi.mlb.com/api/v1"

SIGNAL_RECORDS_CSV_PATH = Path(__file__).resolve().parent / "data" / "signal_records.csv"

SIGNAL_RECORD_FIELDNAMES = [
    "game_id",
    "game_date",
    "away_team",
    "home_team",
    "away_strength",
    "home_strength",
    "signed_strength_gap",
    "strength_gap",
    "competitiveness_score",
    "smg_total_gap",
    "smg_competitiveness",
    "smg_confidence",
    "overall_confidence",
    "away_score",
    "home_score",
    "away_won",
]

# ----------------------------------------------------------------------
# Baseball Savant custom leaderboard is now the PRIMARY hitter source.
# OPS+ is not provided by this Savant custom leaderboard, so it remains
# missing-safe (None) unless you later add another source explicitly.
# ----------------------------------------------------------------------
SAVANT_CUSTOM_LEADERBOARD_URL = (
    "https://baseballsavant.mlb.com/leaderboard/custom"
    "?year={season}"
    "&type=batter"
    "&filter="
    "&min=10"
    "&selections="
    "pa,"
    "k_percent,"
    "bb_percent,"
    "slg_percent,"
    "on_base_percent,"
    "isolated_power,"
    "xba,"
    "xslg,"
    "xwoba,"
    "sweet_spot_percent,"
    "barrel_batted_rate,"
    "hard_hit_percent,"
    "avg_best_speed,"
    "avg_hyper_speed,"
    "whiff_percent,"
    "swing_percent,"
    "sprint_speed"
    "&chart=false"
    "&x=pa"
    "&y=pa"
    "&r=no"
    "&chartType=beeswarm"
    "&sort=xwoba"
    "&sortDir=desc"
)

HTTP_HEADERS = {
    "User-Agent": (
        "Mozilla/5.0 (Windows NT 10.0; Win64; x64) "
        "AppleWebKit/537.36 (KHTML, like Gecko) "
        "Chrome/124.0 Safari/537.36"
    ),
    "Referer": "https://baseballsavant.mlb.com/",
    "Accept": "text/csv,application/json,text/plain,*/*",
}

DESIRED_PITCHER_STAT_KEYS = {
    "HR": ("homeRuns", "homeRunsAllowed"),
    "SO": ("strikeOuts", "strikeouts"),
    "AVG": ("avg", "opponentAvg", "battingAverageAgainst"),
    "BB": ("baseOnBalls", "walks"),
    "WHIP": ("whip", "walksAndHitsPerInningPitched"),
}

DESIRED_TEAM_DEFENSIVE_COLUMNS = [
    "putOuts",
    "assists",
    "errors",
    "doublePlays",
    "fielding",
]

DESIRED_BATTER_STAT_KEYS = [
    "avg",
    "obp",
    "slg",
    "ops",
    "homeRuns",
    "rbi",
    "strikeOuts",
    "baseOnBalls",
]

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

TEAM_ID_MAP = {
    "arizona diamondbacks": 109,
    "atlanta braves": 144,
    "baltimore orioles": 110,
    "boston red sox": 111,
    "chicago cubs": 112,
    "chicago white sox": 145,
    "cincinnati reds": 113,
    "cleveland guardians": 114,
    "colorado rockies": 115,
    "detroit tigers": 116,
    "houston astros": 117,
    "kansas city royals": 118,
    "los angeles angels": 108,
    "los angeles dodgers": 119,
    "miami marlins": 146,
    "milwaukee brewers": 158,
    "minnesota twins": 142,
    "new york mets": 121,
    "new york yankees": 147,
    "athletics": 133,
    "philadelphia phillies": 143,
    "pittsburgh pirates": 134,
    "san diego padres": 135,
    "san francisco giants": 137,
    "seattle mariners": 136,
    "st louis cardinals": 138,
    "tampa bay rays": 139,
    "texas rangers": 140,
    "toronto blue jays": 141,
    "washington nationals": 120,
}

league_means = {
    "OPS": 0.720,
    "OBP": 0.315,
    "SLG": 0.390,
    "HR": 12.0,
    "BB": 28.0,
    "SO": 75.0,
    "WHIP": 1.30,
    "AVG": 0.245,
    "FldPct": 0.985,
    "E": 20.0,
    "DP": 25.0,
}

league_stds = {
    "OPS": 0.050,
    "OBP": 0.020,
    "SLG": 0.040,
    "HR": 4.0,
    "BB": 8.0,
    "SO": 15.0,
    "WHIP": 0.15,
    "AVG": 0.020,
    "FldPct": 0.005,
    "E": 8.0,
    "DP": 8.0,
}

# Normalization scales for same-metric gap comparisons.
# Each value is one "typical unit of difference" between two teams for that metric.
METRIC_COMPARISON_SCALES: dict[str, float] = {
    # Pitcher
    "WHIP": 0.15,
    "AVG_allowed": 0.020,
    "BB": 8.0,
    "HR": 4.0,
    "SO": 15.0,
    "IP": 30.0,
    "gamesPlayed": 5.0,
    "gamesStarted": 4.0,
    # Defense
    "fielding": 0.005,
    "errors": 8.0,
    "doublePlays": 8.0,
    "putOuts": 100.0,
    "assists": 80.0,
    # Offense (team-averaged lineup stats)
    "OBP": 0.020,
    "SLG": 0.040,
    "OPS": 0.050,
    "ISO": 0.030,
    "xwOBA": 0.025,
    "xBA": 0.020,
    "xSLG": 0.040,
    "BB%": 2.5,
    "K%": 4.0,
    "Barrel%": 2.5,
    "HardHit%": 5.0,
    "SweetSpot%": 4.0,
    "AvgEV": 2.5,
    "SprintSpeed": 0.5,
    "lineup_score": 0.05,
}

# Per-metric weights used when combining normalized gaps into component scores.
PITCHER_GAP_WEIGHTS: dict[str, float] = {
    "WHIP": 0.30,
    "AVG_allowed": 0.15,
    "BB": 0.12,
    "HR": 0.13,
    "SO": 0.15,
    "IP": 0.08,
    "gamesPlayed": 0.04,
    "gamesStarted": 0.03,
}

DEFENSE_GAP_WEIGHTS: dict[str, float] = {
    "fielding": 0.40,
    "errors": 0.30,
    "doublePlays": 0.15,
    "putOuts": 0.08,
    "assists": 0.07,
}

OFFENSE_GAP_WEIGHTS: dict[str, float] = {
    "OBP": 0.10,
    "SLG": 0.08,
    "OPS": 0.10,
    "ISO": 0.07,
    "xwOBA": 0.12,
    "xBA": 0.06,
    "xSLG": 0.07,
    "BB%": 0.06,
    "K%": 0.06,
    "Barrel%": 0.07,
    "HardHit%": 0.05,
    "SweetSpot%": 0.04,
    "AvgEV": 0.05,
    "SprintSpeed": 0.04,
    "lineup_score": 0.03,
}

LINEUP_SPOT_WEIGHTS = {
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

HITTER_GROUPS = {
    "G1_top_1_3": {
        "slots": {1, 2, 3},
        "stats": ["OBP", "BB%", "K%", "SprintSpeed"],
        "stat_weights": {
            "OBP": 0.35,
            "BB%": 0.20,
            "K%": 0.20,
            "SprintSpeed": 0.25,
        },
    },
    "G2_mid_3_6": {
        "slots": {3, 4, 5, 6},
        "stats": ["ISO", "SLG", "xwOBA", "xSLG", "Barrel%", "HardHit%", "AvgEV", "SweetSpot%"],
        "stat_weights": {
            "ISO": 0.12,
            "SLG": 0.12,
            "xwOBA": 0.18,
            "xSLG": 0.16,
            "Barrel%": 0.14,
            "HardHit%": 0.10,
            "AvgEV": 0.08,
            "SweetSpot%": 0.10,
        },
    },
    "G3_bot_7_9": {
        "slots": {7, 8, 9},
        "stats": ["OPS", "OBP", "K%", "xBA"],
        "stat_weights": {
            "OPS": 0.35,
            "OBP": 0.30,
            "K%": 0.20,
            "xBA": 0.15,
        },
    },
}

_SAVANT_BATTING_CACHE: dict[int, pd.DataFrame] = {}

PLAYER_GROUP_BLEND_WEIGHTS = {
    1: {"G1_top_1_3": 1.00},
    2: {"G1_top_1_3": 1.00},
    3: {"G1_top_1_3": 0.45, "G2_mid_3_6": 0.55},
    4: {"G2_mid_3_6": 1.00},
    5: {"G2_mid_3_6": 1.00},
    6: {"G2_mid_3_6": 1.00},
    7: {"G3_bot_7_9": 1.00},
    8: {"G3_bot_7_9": 1.00},
    9: {"G3_bot_7_9": 1.00},
}


def normalize_text(value: str | None) -> str:
    if not value:
        return ""
    text = unicodedata.normalize("NFKD", value)
    text = "".join(ch for ch in text if not unicodedata.combining(ch))
    text = text.lower().strip()
    text = re.sub(r"[^\w\s%/,\.-]", "", text)
    text = re.sub(r"\s+", " ", text)
    return text


TEAM_ALIAS_LOOKUP = {}
for canonical_name, aliases in TEAM_NAME_ALIASES.items():
    TEAM_ALIAS_LOOKUP[normalize_text(canonical_name)] = canonical_name
    for alias in aliases:
        TEAM_ALIAS_LOOKUP[normalize_text(alias)] = canonical_name


def normalize_player_name(name: str | None) -> str:
    return normalize_text(name)


def normalize_player_name_last_first(name: str | None) -> str:
    """
    Converts 'Munetaka Murakami' -> 'murakami, munetaka'
    and also normalizes accents / punctuation / spacing.
    """
    if not name:
        return ""
    parts = re.split(r"\s+", name.strip())
    if len(parts) < 2:
        return normalize_text(name)
    first = " ".join(parts[:-1])
    last = parts[-1]
    return normalize_text(f"{last}, {first}")


def canonicalize_team_name(team_name: str | None) -> str:
    normalized = normalize_text(team_name)
    if not normalized:
        return ""
    if normalized in TEAM_ALIAS_LOOKUP:
        return TEAM_ALIAS_LOOKUP[normalized]
    return normalized


def canonicalize_team_name_from_page(team_name: str | None) -> str:
    if not team_name:
        return ""

    normalized = normalize_text(team_name)
    if normalized in TEAM_ALIAS_LOOKUP:
        return TEAM_ALIAS_LOOKUP[normalized]

    upper = re.sub(r"[^A-Z]", "", team_name.upper())
    if upper in TEAM_ABBREV_TO_CANONICAL:
        return TEAM_ABBREV_TO_CANONICAL[upper]

    canonical = canonicalize_team_name(team_name)
    if canonical:
        return canonical

    return normalized


def split_first_last_name(full_name: str) -> tuple[str, str]:
    parts = (full_name or "").strip().split()
    if not parts:
        return "", ""
    if len(parts) == 1:
        return parts[0], parts[0]
    return parts[0], parts[-1]


def safe_pct_to_float(value: Any, default: Optional[float] = None) -> Optional[float]:
    if value in (None, "", "N/A"):
        return default
    try:
        if isinstance(value, str):
            text = value.strip().replace("%", "").replace(",", "")
            return float(text)
        return float(value)
    except Exception:
        return default


def safe_float(x, default=None):
    try:
        if x in ("N/A", None, ""):
            return default
        if isinstance(x, str):
            x = x.replace(",", "").strip()
        return float(x)
    except Exception:
        return default


def parse_innings_pitched(ip_value) -> Optional[float]:
    """
    Convert MLB innings format to decimal innings.
    "12.1" means 12 and 1/3 innings (1 out recorded), not 12.1 decimal.
    "12.2" means 12 and 2/3 innings.
    """
    v = safe_float(ip_value)
    if v is None:
        return None
    whole = int(v)
    outs = round((v - whole) * 10)
    if outs > 2:
        return v
    return whole + outs / 3.0


def pitcher_reliability_factor(ip_decimal: float) -> float:
    """
    Sample-size confidence weight in [0, 1] based on innings pitched this season.
    Reaches 1.0 at PITCHER_FULL_SEASON_IP. Uses sqrt curve so early IP still
    contributes meaningfully while small samples stay appropriately discounted.
    Examples: 10 IP → 0.25, 40 IP → 0.50, 81 IP → 0.71, 162 IP → 1.0.
    """
    if ip_decimal <= 0.0:
        return 0.0
    return min(ip_decimal / PITCHER_FULL_SEASON_IP, 1.0) ** 0.5


def get_first_value_from_row(row: Optional[pd.Series], candidates: list[str], default: Any = None) -> Any:
    if row is None:
        return default

    for cand in candidates:
        if cand in row.index:
            value = row.get(cand)
            if value not in (None, "", "N/A") and not pd.isna(value):
                return value

    lower_index = {str(k).lower(): k for k in row.index}
    for cand in candidates:
        actual = lower_index.get(cand.lower())
        if actual is not None:
            value = row.get(actual)
            if value not in (None, "", "N/A") and not pd.isna(value):
                return value

    return default


def normalize_stat_for_scoring(stat_name: str, value: Optional[float]) -> Optional[float]:
    if value is None:
        return None

    if stat_name in {"OPS"}:
        return value / 100.0

    if stat_name in {"OBP", "SLG", "ISO", "xwOBA", "xBA", "xSLG"}:
        return value

    if stat_name in {"BB%", "K%", "Barrel%", "HardHit%", "SweetSpot%"}:
        return value / 100.0

    if stat_name == "SprintSpeed":
        return max(min((value - 23.0) / 8.0, 1.5), -0.5)

    if stat_name == "AvgEV":
        return max(min((value - 80.0) / 20.0, 1.5), -0.5)

    return value


def weighted_mean_ignore_missing(values: dict[str, Optional[float]], weights: dict[str, float]) -> tuple[float, float]:
    used = []
    for stat_name, weight in weights.items():
        v = values.get(stat_name)
        if v is not None:
            used.append((v, weight))

    if not used:
        return 0.0, 0.0

    numerator = sum(v * w for v, w in used)
    denom = sum(w for _, w in used)
    confidence = denom / sum(weights.values()) if weights else 0.0
    return numerator / denom, confidence


def get_player_group_names(slot: int) -> list[str]:
    return list(PLAYER_GROUP_BLEND_WEIGHTS.get(slot, {}).keys())


# ----------------------------------------------------------------------
# NEW: single-source Baseball Savant custom leaderboard fetch.
# This replaces the old Baseball Reference / fragmented Statcast hitter
# extraction path.
# ----------------------------------------------------------------------
def _looks_like_csv_payload(text: str) -> bool:
    text = (text or "").strip()
    if not text:
        return False
    if "<html" in text.lower():
        return False
    first_line = text.splitlines()[0] if text.splitlines() else ""
    return "," in first_line


def _normalize_savant_dataframe(df: pd.DataFrame) -> pd.DataFrame:
    if df is None or df.empty:
        return pd.DataFrame()

    out = df.copy()
    out.columns = [str(c).strip() for c in out.columns]

    rename_map: dict[str, str] = {}
    for col in out.columns:
        col_norm = normalize_text(col)

        if col_norm in {"player_id", "mlbam_id"}:
            rename_map[col] = "player_id"
        elif col_norm in {"last_name first_name", "last_name, first_name", "player_name", "name"}:
            rename_map[col] = "player_name"
        elif col_norm in {"team", "team_abbr"}:
            rename_map[col] = "team"
        elif col_norm in {"on_base_percent", "obp"}:
            rename_map[col] = "OBP"
        elif col_norm in {"bb_percent", "bb%"}:
            rename_map[col] = "BB%"
        elif col_norm in {"k_percent", "k%"}:
            rename_map[col] = "K%"
        elif col_norm in {"isolated_power", "iso"}:
            rename_map[col] = "ISO"
        elif col_norm in {"slg_percent", "slg"}:
            rename_map[col] = "SLG"
        elif col_norm in {"xba", "xba"}:
            rename_map[col] = "xBA"
        elif col_norm in {"xslg", "xslg"}:
            rename_map[col] = "xSLG"
        elif col_norm in {"xwoba", "xwoba"}:
            rename_map[col] = "xwOBA"
        elif col_norm in {"barrel_batted_rate", "barrel%", "barrel_percent", "barrel rate"}:
            rename_map[col] = "Barrel%"
        elif col_norm in {"hard_hit_percent", "hard hit %", "hard_hit%"}:
            rename_map[col] = "HardHit%"
        elif col_norm in {"sweet_spot_percent", "la sweet-spot %", "la sweet spot %"}:
            rename_map[col] = "SweetSpot%"
        elif col_norm in {"avg_best_speed", "avg ev mph", "avg ev", "avg_ev", "exit_velocity_avg", "avg_hit_speed"}:
            rename_map[col] = "AvgEV"
        elif col_norm in {"sprint_speed", "sprint speed"}:
            rename_map[col] = "SprintSpeed"

    out = out.rename(columns=rename_map)

    # Ensure expected columns exist even if missing from payload.
    for needed in [
        "player_id", "player_name", "team",
        "OBP", "BB%", "K%", "ISO", "SLG",
        "xBA", "xSLG", "xwOBA",
        "Barrel%", "HardHit%", "SweetSpot%",
        "AvgEV", "SprintSpeed",
    ]:
        if needed not in out.columns:
            out[needed] = None

    # Normalize ids and names.
    out["player_id"] = out["player_id"].apply(lambda x: int(float(x)) if safe_float(x) is not None else None)
    out["player_name_norm"] = out["player_name"].astype(str).map(normalize_player_name)
    out["player_name_last_first_norm"] = out["player_name"].astype(str).map(normalize_player_name)

    return out


def fetch_savant_custom_batting_table(season: int) -> pd.DataFrame:
    """
    Fetches the Baseball Savant custom leaderboard used by the model.

    The page has a CSV download control, but the exact response mode can vary.
    So this function tries a few CSV-oriented variants against the same
    leaderboard parameters and only accepts the response when it looks like CSV.
    """
    if season in _SAVANT_BATTING_CACHE:
        return _SAVANT_BATTING_CACHE[season]

    base_url = SAVANT_CUSTOM_LEADERBOARD_URL.format(season=season)

    candidate_urls = [
        base_url + "&csv=true",
        base_url + "&download=true",
        base_url + "&csv=true&download=true",
        base_url,
    ]

    session = requests.Session()
    df = pd.DataFrame()

    for url in candidate_urls:
        try:
            resp = session.get(url, headers=HTTP_HEADERS, timeout=30)
            resp.raise_for_status()
            text = resp.text

            if not _looks_like_csv_payload(text):
                continue

            temp_df = pd.read_csv(io.StringIO(text))
            if temp_df is not None and not temp_df.empty:
                df = _normalize_savant_dataframe(temp_df)
                break
        except Exception:
            continue

    if df.empty:
        print(f"[WARN] Baseball Savant custom leaderboard fetch failed for season {season}.")
        print("       Hitter advanced stats will remain missing-safe for this run.")

    _SAVANT_BATTING_CACHE[season] = df
    return df


def resolve_player_ids_for_pybaseball(player_name: str) -> dict[str, Any]:
    first, last = split_first_last_name(player_name)
    if not first or not last:
        return {"name": player_name, "key_mlbam": None, "reason": "Could not split first/last name."}

    try:
        df = playerid_lookup(last, first)
    except Exception as exc:
        return {"name": player_name, "key_mlbam": None, "reason": f"playerid_lookup failed: {exc}"}

    if df is None or df.empty:
        return {"name": player_name, "key_mlbam": None, "reason": "No pybaseball lookup match."}

    row = df.iloc[0]
    key_mlbam = None

    for col in ["key_mlbam", "mlbam_id", "mlbam"]:
        if col in row.index and pd.notna(row[col]):
            try:
                key_mlbam = int(float(row[col]))
                break
            except Exception:
                pass

    return {
        "name": player_name,
        "key_mlbam": key_mlbam,
        "reason": None,
    }


def build_name_match_variants(player_name: str) -> set[str]:
    base = normalize_player_name(player_name)
    last_first = normalize_player_name_last_first(player_name)
    variants = {base, last_first}

    # Also support cases where Savant may return "Last, First Middle"
    parts = (player_name or "").strip().split()
    if len(parts) >= 3:
        first = " ".join(parts[:-1])
        last = parts[-1]
        variants.add(normalize_text(f"{last}, {first}"))

    return {v for v in variants if v}


def find_best_savant_player_row(
    df: pd.DataFrame,
    player_name: str,
    mlbam_id: Optional[int] = None,
    current_team: str | None = None,
) -> Optional[pd.Series]:
    if df is None or df.empty:
        return None

    # Prefer exact MLBAM/player_id match whenever available.
    if mlbam_id is not None and "player_id" in df.columns:
        hit = df[df["player_id"] == mlbam_id]
        if not hit.empty:
            if len(hit) == 1:
                return hit.iloc[0]
            if current_team and "team" in hit.columns:
                wanted_team = canonicalize_team_name(current_team)
                for _, row in hit.iterrows():
                    row_team = canonicalize_team_name(str(row.get("team", "")))
                    if row_team == wanted_team:
                        return row
            return hit.iloc[0]

    variants = build_name_match_variants(player_name)

    # Savant typically uses "Last, First".
    temp = df[df["player_name_norm"].isin(variants)]
    if not temp.empty:
        if len(temp) == 1:
            return temp.iloc[0]
        if current_team and "team" in temp.columns:
            wanted_team = canonicalize_team_name(current_team)
            for _, row in temp.iterrows():
                row_team = canonicalize_team_name(str(row.get("team", "")))
                if row_team == wanted_team:
                    return row
        return temp.iloc[0]

    return None


def extract_player_advanced_batting_stats(
    player_name: str,
    season: int,
    current_team: str | None = None,
    mlbam_id_override: Optional[int] = None,
) -> dict[str, Any]:
    """
    New hitter stat extraction path:
    - Primary source: Baseball Savant custom leaderboard
    - Match by MLBAM id first when available
    - Fallback to robust name matching that supports
      'First Last' <-> 'Last, First'
    - Missing values are kept safe as None

    OPS+ is intentionally left as None because this Savant custom leaderboard
    does not expose OPS+ directly.
    """
    id_info = resolve_player_ids_for_pybaseball(player_name)
    mlbam_id = mlbam_id_override if mlbam_id_override is not None else id_info.get("key_mlbam")

    savant_df = fetch_savant_custom_batting_table(season)
    savant_row = find_best_savant_player_row(
        savant_df,
        player_name=player_name,
        mlbam_id=mlbam_id,
        current_team=current_team,
    )

    stats = {
        "lookup_reason": id_info.get("reason"),
        "key_mlbam": mlbam_id,
        "source": "Baseball Savant custom leaderboard",

        "OBP": safe_float(get_first_value_from_row(savant_row, ["OBP"], None)),
        "BB%": safe_pct_to_float(get_first_value_from_row(savant_row, ["BB%"], None)),
        "K%": safe_pct_to_float(get_first_value_from_row(savant_row, ["K%"], None)),
        "ISO": safe_float(get_first_value_from_row(savant_row, ["ISO"], None)),
        "SLG": safe_float(get_first_value_from_row(savant_row, ["SLG"], None)),
        "xwOBA": safe_float(get_first_value_from_row(savant_row, ["xwOBA"], None)),
        "xBA": safe_float(get_first_value_from_row(savant_row, ["xBA"], None)),
        "xSLG": safe_float(get_first_value_from_row(savant_row, ["xSLG"], None)),
        "Barrel%": safe_pct_to_float(get_first_value_from_row(savant_row, ["Barrel%"], None)),
        "HardHit%": safe_pct_to_float(get_first_value_from_row(savant_row, ["HardHit%"], None)),
        "AvgEV": safe_float(get_first_value_from_row(savant_row, ["AvgEV"], None)),
        "SweetSpot%": safe_pct_to_float(get_first_value_from_row(savant_row, ["SweetSpot%"], None)),
        "SprintSpeed": safe_float(get_first_value_from_row(savant_row, ["SprintSpeed"], None)),

        # OPS is not directly present in your current selected Savant leaderboard fields,
        # so compute it as OBP + SLG when both are available.
        "OPS": (
            safe_float(get_first_value_from_row(savant_row, ["OBP"], None)) +
            safe_float(get_first_value_from_row(savant_row, ["SLG"], None))
            if safe_float(get_first_value_from_row(savant_row, ["OBP"], None)) is not None
               and safe_float(get_first_value_from_row(savant_row, ["SLG"], None)) is not None
            else None
        ),
    }

    return stats


def compute_group_score_for_player(slot: int, player_stats: dict[str, Any], group_name: str) -> tuple[float, float]:
    group_cfg = HITTER_GROUPS[group_name]
    group_weights = group_cfg["stat_weights"]

    values: dict[str, Optional[float]] = {}
    for stat_name in group_weights:
        raw = player_stats.get(stat_name)
        if stat_name == "K%":
            norm = normalize_stat_for_scoring(stat_name, raw)
            values[stat_name] = None if norm is None else -norm
        else:
            values[stat_name] = normalize_stat_for_scoring(stat_name, raw)

    score, confidence = weighted_mean_ignore_missing(values, group_weights)
    return score, confidence


def compute_player_lineup_contribution(slot: int, player_stats: dict[str, Any]) -> dict[str, Any]:
    blend_weights = PLAYER_GROUP_BLEND_WEIGHTS.get(slot, {})
    if not blend_weights:
        return {
            "group_scores": {},
            "group_confidences": {},
            "base_player_score": 0.0,
            "player_score_confidence": 0.0,
            "lineup_spot_weight": LINEUP_SPOT_WEIGHTS.get(slot, 1.0),
            "weighted_contribution": 0.0,
        }

    group_scores: dict[str, float] = {}
    group_confidences: dict[str, float] = {}

    for group_name in blend_weights:
        g_score, g_conf = compute_group_score_for_player(slot, player_stats, group_name)
        group_scores[group_name] = g_score
        group_confidences[group_name] = g_conf

    used = []
    for group_name, blend_w in blend_weights.items():
        used.append((group_scores[group_name], blend_w))

    base_player_score = sum(score * w for score, w in used) / sum(w for _, w in used)
    player_score_confidence = (
        sum(group_confidences[g] * w for g, w in blend_weights.items()) / sum(blend_weights.values())
    )

    lineup_spot_weight = LINEUP_SPOT_WEIGHTS.get(slot, 1.0)
    weighted_contribution = base_player_score * lineup_spot_weight

    return {
        "group_scores": group_scores,
        "group_confidences": group_confidences,
        "base_player_score": base_player_score,
        "player_score_confidence": player_score_confidence,
        "lineup_spot_weight": lineup_spot_weight,
        "weighted_contribution": weighted_contribution,
    }


def build_live_lineup_player_id_lookup(lineup_block: dict[str, Any]) -> dict[str, int]:
    lookup: dict[str, int] = {}
    for batter in lineup_block.get("batters", []):
        player_id = batter.get("player_id")
        name = batter.get("name")
        if player_id and name:
            lookup[normalize_player_name(name)] = int(player_id)
    return lookup


def enrich_announced_team_players_with_lineup_scores(
    players: list[dict[str, str]],
    season: int,
    team_name: str | None = None,
    live_player_id_lookup: Optional[dict[str, int]] = None,
) -> list[dict[str, Any]]:
    enriched: list[dict[str, Any]] = []

    live_player_id_lookup = live_player_id_lookup or {}

    for idx, player in enumerate(players, start=1):
        name = player.get("name", "N/A")
        position = player.get("position", "N/A")

        handedness = "N/A"
        m = re.search(r"\(([RLS])\)", name)
        if m:
            handedness = m.group(1)

        clean_name = re.sub(r"\s*\([RLS]\)\s*$", "", name).strip()
        mlbam_id_override = live_player_id_lookup.get(normalize_player_name(clean_name))

        adv_stats = extract_player_advanced_batting_stats(
            clean_name,
            season,
            current_team=team_name,
            mlbam_id_override=mlbam_id_override,
        )
        contrib = compute_player_lineup_contribution(idx, adv_stats)

        enriched.append(
            {
                "batting_order": idx,
                "name": clean_name,
                "raw_name": name,
                "handedness": handedness,
                "position": position,
                "groups": get_player_group_names(idx),
                "advanced_stats": adv_stats,
                "group_scores": contrib["group_scores"],
                "group_confidences": contrib["group_confidences"],
                "base_player_score": contrib["base_player_score"],
                "player_score_confidence": contrib["player_score_confidence"],
                "lineup_spot_weight": contrib["lineup_spot_weight"],
                "weighted_contribution": contrib["weighted_contribution"],
            }
        )

    return enriched


def build_team_lineup_segment_score(enriched_players: list[dict[str, Any]]) -> dict[str, Any]:
    if not enriched_players:
        return {
            "team_lineup_score": 0.0,
            "avg_confidence": 0.0,
            "group_subtotals": {},
        }

    weighted_sum = sum(p["weighted_contribution"] for p in enriched_players)
    total_spot_weight = sum(p["lineup_spot_weight"] for p in enriched_players) or 1.0
    team_lineup_score = weighted_sum / total_spot_weight

    avg_confidence = sum(p["player_score_confidence"] for p in enriched_players) / len(enriched_players)

    group_subtotals = {}
    for group_name in HITTER_GROUPS:
        vals = []
        for p in enriched_players:
            if group_name in p["group_scores"]:
                vals.append(p["group_scores"][group_name])
        group_subtotals[group_name] = (sum(vals) / len(vals)) if vals else 0.0

    return {
        "team_lineup_score": team_lineup_score,
        "avg_confidence": avg_confidence,
        "group_subtotals": group_subtotals,
    }


def fmt_stat(v: Any, digits: int = 3) -> str:
    if v in (None, "", "N/A"):
        return "N/A"
    try:
        return f"{float(v):.{digits}f}"
    except Exception:
        return str(v)


# ----------------------------------------------------------------------
# Everything below this line can stay exactly as in your current script,
# EXCEPT for the two enrich_announced_team_players_with_lineup_scores(...)
# calls inside main(), which should be updated as shown further below.
# ----------------------------------------------------------------------

# Matches any separator MLB may use between away and home team names.
# Handles "@", "at", "vs", "vs." (case-insensitive, surrounded by whitespace).
_MATCHUP_SEP_RE = re.compile(r"\s+(?:@|at|vs\.?)\s+", re.IGNORECASE)


def split_matchup_title(title: str | None) -> tuple[Optional[str], Optional[str]]:
    """
    Split a matchup string into (away, home).
    Handles separators: '@', 'at', 'vs', 'vs.'
    Examples:
      'Houston Astros @ Cincinnati Reds'  -> ('Houston Astros', 'Cincinnati Reds')
      'Astros at Reds'                    -> ('Astros', 'Reds')
      'HOU vs CIN'                        -> ('HOU', 'CIN')
    """
    if not title:
        return None, None

    text = re.sub(r"\s+", " ", title).strip()
    m = _MATCHUP_SEP_RE.search(text)
    if not m:
        return None, None

    away = text[: m.start()].strip()
    home = text[m.end() :].strip()

    if not away or not home:
        return None, None

    return away, home


def canonicalize_matchup_title(title: str | None) -> tuple[Optional[str], Optional[str]]:
    away_raw, home_raw = split_matchup_title(title)
    if not away_raw or not home_raw:
        return None, None

    away_canon = canonicalize_team_name_from_page(away_raw)
    home_canon = canonicalize_team_name_from_page(home_raw)

    if not away_canon or not home_canon:
        return None, None

    return away_canon, home_canon


def parse_game_datetime_utc(game: dict) -> datetime | None:
    for value in (game.get("game_datetime"), game.get("game_date"), game.get("datetime")):
        if not value or not isinstance(value, str):
            continue
        text = value.strip()
        if not text:
            continue
        if text.endswith("Z"):
            text = text[:-1] + "+00:00"
        try:
            dt = datetime.fromisoformat(text)
            if dt.tzinfo is None:
                dt = dt.replace(tzinfo=timezone.utc)
            return dt.astimezone(timezone.utc)
        except ValueError:
            continue
    return None


def get_games_starting_within_next_hours(hours: int = LOOKAHEAD_HOURS):
    now_utc = datetime.now(timezone.utc)
    window_end_utc = now_utc + timedelta(hours=hours)

    # Analysis date = "today" in the USA (US Eastern), i.e. the MLB schedule day.
    eastern = ZoneInfo("America/New_York")
    analysis_date_usa = now_utc.astimezone(eastern).date()

    # Fetch the analysis-date schedule plus the window boundary dates so both
    # already-started games on the analysis date and upcoming games are covered.
    dates_to_fetch = {
        now_utc.date().isoformat(),
        window_end_utc.date().isoformat(),
        analysis_date_usa.isoformat(),
    }
    upcoming_games = []
    seen_game_ids = set()

    for date_str in sorted(dates_to_fetch):
        games = statsapi.schedule(date=date_str)
        for game in games:
            game_dt = parse_game_datetime_utc(game)
            if game_dt is None:
                continue

            # Keep a game if either:
            #  (a) it starts within the look-ahead window, or
            #  (b) it already started AND its USA (Eastern) date is the
            #      analysis date — i.e. a game from today that is already underway.
            in_window = now_utc <= game_dt <= window_end_utc
            already_started_today = (
                game_dt <= now_utc
                and game_dt.astimezone(eastern).date() == analysis_date_usa
            )
            if not (in_window or already_started_today):
                continue

            game_id = game.get("game_id")
            if game_id in seen_game_ids:
                continue

            seen_game_ids.add(game_id)
            game["parsed_game_datetime_utc"] = game_dt
            upcoming_games.append(game)

    upcoming_games.sort(key=lambda g: g["parsed_game_datetime_utc"])
    return upcoming_games


def choose_best_player_match(player_name: str, matches: list[dict[str, Any]]) -> Optional[dict[str, Any]]:
    if not matches:
        return None

    wanted = normalize_player_name(player_name)

    for row in matches:
        full_name = normalize_player_name(row.get("fullName") or row.get("nameFirstLast"))
        if full_name == wanted:
            return row

    for row in matches:
        display_name = normalize_player_name(row.get("fullFMLName") or row.get("fullName"))
        if display_name == wanted:
            return row

    for row in matches:
        if row.get("active") is True:
            return row

    return matches[0]


def get_pitcher_id(pitcher_name: str | None) -> tuple[Optional[int], Optional[str]]:
    if not pitcher_name:
        return None, "No probable pitcher listed for this game yet."

    try:
        matches = statsapi.lookup_player(pitcher_name)
    except Exception as exc:
        return None, f"lookup_player failed: {exc}"

    if not matches:
        return None, f"No player match found in statsapi.lookup_player for '{pitcher_name}'."

    best = choose_best_player_match(pitcher_name, matches)
    if not best:
        return None, f"No suitable player match found for '{pitcher_name}'."

    player_id = best.get("id")
    if not player_id:
        return None, f"Matched player for '{pitcher_name}', but no player id was returned."

    return int(player_id), None


def fetch_pitcher_season_stat_row(player_id: int, season: int) -> tuple[Optional[dict[str, Any]], Optional[str]]:
    url = f"{MLB_STATS_API_BASE}/people/{player_id}/stats"
    params = {
        "stats": "season",
        "group": "pitching",
        "sportIds": 1,
        "season": season,
    }

    try:
        response = requests.get(url, params=params, timeout=20)
        response.raise_for_status()
        payload = response.json()
    except Exception as exc:
        return None, f"Failed to fetch person stats for player_id={player_id}: {exc}"

    stats_blocks = payload.get("stats", [])
    if not stats_blocks:
        return None, "No 'stats' blocks returned by MLB person stats endpoint."

    for block in stats_blocks:
        splits = block.get("splits", [])
        if not splits:
            continue
        first = splits[0]
        stat_row = first.get("stat")
        if isinstance(stat_row, dict) and stat_row:
            return stat_row, None

    return None, "No season pitching stat row found in person stats response."


def get_first_present_stat(stat_row: dict[str, Any], aliases: tuple[str, ...]) -> tuple[Optional[Any], Optional[str]]:
    for key in aliases:
        if key in stat_row and stat_row[key] not in (None, ""):
            return stat_row[key], key
    return None, None


def get_pitcher_metric_block(pitcher_name: str | None, season: int) -> dict[str, Any]:
    result: dict[str, Any] = {
        "pitcher": pitcher_name or "N/A",
        "player_id": None,
        "source": None,
        "global_reason": None,
        "gamesPlayed": None,
        "gamesStarted": None,
        "inningsPitched": None,
        "inningsPitched_decimal": None,
        "reliability": 0.0,
    }

    for label in DESIRED_PITCHER_STAT_KEYS:
        result[f"{label} value"] = "N/A"
        result[f"{label} source_key"] = None
        result[f"{label} reason"] = None

    player_id, id_reason = get_pitcher_id(pitcher_name)
    if player_id is None:
        result["global_reason"] = id_reason
        for label in DESIRED_PITCHER_STAT_KEYS:
            result[f"{label} reason"] = id_reason
        return result

    result["player_id"] = player_id

    stat_row, stat_reason = fetch_pitcher_season_stat_row(player_id, season)
    if stat_row is None:
        result["global_reason"] = stat_reason
        for label in DESIRED_PITCHER_STAT_KEYS:
            result[f"{label} reason"] = stat_reason
        return result

    result["source"] = "MLB person stats endpoint"

    ip_raw = stat_row.get("inningsPitched")
    ip_decimal = parse_innings_pitched(ip_raw)
    result["gamesPlayed"] = stat_row.get("gamesPlayed")
    result["gamesStarted"] = stat_row.get("gamesStarted")
    result["inningsPitched"] = ip_raw
    result["inningsPitched_decimal"] = ip_decimal
    result["reliability"] = pitcher_reliability_factor(ip_decimal or 0.0)

    for label, aliases in DESIRED_PITCHER_STAT_KEYS.items():
        value, source_key = get_first_present_stat(stat_row, aliases)
        if value is None:
            result[f"{label} reason"] = (
                f"Stat not present in the player's season pitching stat row. "
                f"Tried keys: {', '.join(aliases)}."
            )
        else:
            result[f"{label} value"] = value
            result[f"{label} source_key"] = source_key

    return result


def get_team_id(team_name: str | None) -> tuple[Optional[int], Optional[str]]:
    if not team_name:
        return None, "No team name provided."

    canonical = canonicalize_team_name(team_name)
    team_id = TEAM_ID_MAP.get(canonical)

    if team_id is None:
        return None, f"Could not map team '{team_name}' to an MLB team ID."

    return team_id, None


def fetch_team_fielding_stat_row(team_id: int, season: int) -> tuple[Optional[dict[str, Any]], Optional[str]]:
    url = f"{MLB_STATS_API_BASE}/teams/{team_id}/stats"
    params = {
        "stats": "season",
        "group": "fielding",
        "sportIds": 1,
        "season": season,
    }

    try:
        response = requests.get(url, params=params, timeout=20)
        response.raise_for_status()
        payload = response.json()
    except Exception as exc:
        return None, f"Failed to fetch team fielding stats for team_id={team_id}: {exc}"

    stats_blocks = payload.get("stats", [])
    if not stats_blocks:
        return None, "No 'stats' blocks returned by MLB team stats endpoint."

    for block in stats_blocks:
        splits = block.get("splits", [])
        if not splits:
            continue
        first = splits[0]
        stat_row = first.get("stat")
        if isinstance(stat_row, dict) and stat_row:
            return stat_row, None

    return None, "No season fielding stat row found in team stats response."


def get_team_defensive_block(team_name: str | None, season: int) -> dict[str, Any]:
    result = {
        "team_name_source": team_name or "N/A",
        "source": "MLB team stats endpoint",
        "stat_type": "team defensive stats",
        "team_id": None,
        "reason": None,
        "putOuts": "N/A",
        "assists": "N/A",
        "errors": "N/A",
        "doublePlays": "N/A",
        "fielding": "N/A",
    }

    team_id, reason = get_team_id(team_name)
    if team_id is None:
        result["reason"] = reason
        return result

    result["team_id"] = team_id

    stat_row, reason = fetch_team_fielding_stat_row(team_id, season)
    if stat_row is None:
        result["reason"] = reason
        return result

    for key in DESIRED_TEAM_DEFENSIVE_COLUMNS:
        if stat_row.get(key) not in (None, ""):
            result[key] = stat_row[key]

    return result


def fetch_game_live_feed(game_pk: int) -> tuple[Optional[dict[str, Any]], Optional[str]]:
    # MLB live feed requires v1.1, not v1.
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


def get_batter_stat_value(player_block: dict[str, Any], key: str) -> Any:
    stat = ((player_block.get("stats") or {}).get("batting") or {})
    return stat.get(key, "N/A")


def extract_team_lineup_from_live_feed(
    live_feed: dict[str, Any],
    side: str,
) -> dict[str, Any]:
    result = {
        "source": "MLB live game feed",
        "stat_type": "batting lineup",
        "side": side,
        "confirmed": False,
        "reason": None,
        "batters": [],
    }

    boxscore_teams = (((live_feed.get("liveData") or {}).get("boxscore") or {}).get("teams") or {})
    team_block = boxscore_teams.get(side) or {}
    batting_order = team_block.get("battingOrder") or []
    players = team_block.get("players") or {}

    if not batting_order:
        result["reason"] = f"No batting order published yet for {side} team."
        return result

    batters = []
    for order_index, player_ref in enumerate(batting_order, start=1):
        player_key = f"ID{player_ref}" if not str(player_ref).startswith("ID") else str(player_ref)
        player_block = players.get(player_key) or {}
        person = player_block.get("person") or {}
        position = (player_block.get("position") or {}).get("abbreviation", "N/A")
        status_desc = ((player_block.get("status") or {}).get("description")) or "N/A"

        batter = {
            "batting_order": order_index,
            "player_id": person.get("id"),
            "name": person.get("fullName", "N/A"),
            "position": position,
            "status": status_desc,
            "stats_source": "MLB live game feed batting season stats",
        }
        batters.append(batter)

    result["confirmed"] = True
    result["batters"] = batters
    return result


def get_game_lineups(game_pk: int) -> dict[str, Any]:
    live_feed, reason = fetch_game_live_feed(game_pk)
    if live_feed is None:
        return {
            "away": {
                "source": "MLB live game feed",
                "stat_type": "batting lineup",
                "side": "away",
                "confirmed": False,
                "reason": reason,
                "batters": [],
            },
            "home": {
                "source": "MLB live game feed",
                "stat_type": "batting lineup",
                "side": "home",
                "confirmed": False,
                "reason": reason,
                "batters": [],
            },
        }

    return {
        "away": extract_team_lineup_from_live_feed(live_feed, "away"),
        "home": extract_team_lineup_from_live_feed(live_feed, "home"),
    }


def build_starting_lineups_url_from_game_dt(game_dt_utc: datetime | None) -> str:
    eastern = ZoneInfo("America/New_York")
    target_dt = game_dt_utc.astimezone(eastern) if game_dt_utc else datetime.now(eastern)
    date_str = target_dt.date().isoformat()
    return f"https://www.mlb.com/starting-lineups/{date_str}"


_MLB_PAGE_HEADERS = {
    "User-Agent": (
        "Mozilla/5.0 (Windows NT 10.0; Win64; x64) "
        "AppleWebKit/537.36 (KHTML, like Gecko) "
        "Chrome/124.0.0.0 Safari/537.36"
    ),
    "Accept": "text/html,application/xhtml+xml,application/xml;q=0.9,image/avif,image/webp,*/*;q=0.8",
    "Accept-Language": "en-US,en;q=0.9",
    "Accept-Encoding": "gzip, deflate, br",
    "Connection": "keep-alive",
    "Upgrade-Insecure-Requests": "1",
    "Sec-Fetch-Dest": "document",
    "Sec-Fetch-Mode": "navigate",
    "Sec-Fetch-Site": "none",
    "Sec-Fetch-User": "?1",
    "Cache-Control": "max-age=0",
    "Referer": "https://www.mlb.com/",
}


def fetch_starting_lineups_page_html(game_dt_utc: datetime | None) -> tuple[Optional[str], Optional[str], Optional[str]]:
    url = build_starting_lineups_url_from_game_dt(game_dt_utc)
    session = requests.Session()
    session.headers.update(_MLB_PAGE_HEADERS)
    try:
        # Prime session with a root hit so cookies/headers flow naturally.
        session.get("https://www.mlb.com/", timeout=15)
        response = session.get(url, timeout=20)
        response.raise_for_status()
        return response.text, url, None
    except Exception as exc:
        return None, None, f"Failed to fetch MLB starting lineups page {url}: {exc}"


def fetch_starting_lineups_page_text(game_dt_utc: datetime | None) -> tuple[Optional[str], Optional[str], Optional[str]]:
    page_html, url, reason = fetch_starting_lineups_page_html(game_dt_utc)
    if page_html is None:
        return None, url, reason

    soup = BeautifulSoup(page_html, "html.parser")
    text = soup.get_text("\n", strip=True)
    return text, url, None


def normalize_line(text: str) -> str:
    return re.sub(r"\s+", " ", (text or "").strip())


def is_matchup_header(line: str) -> bool:
    return bool(_MATCHUP_SEP_RE.search(line)) and not line.startswith("http")


def is_lineup_label(line: str) -> bool:
    return bool(re.match(r"^[A-Z]{2,3}\s+Lineup$", line))


def is_batter_line(line: str) -> bool:
    return bool(re.match(r"^\d+\.\s+.+$", line))


def extract_batter_name_from_line(line: str) -> str:
    m = re.match(r"^\d+\.\s+(.+?)\s+\(([RLS])\)\s+[A-Z0-9]+$", line)
    if m:
        return m.group(1).strip()

    m = re.match(r"^\d+\.\s+(.+?)\s+\([RLS]\)", line)
    if m:
        return m.group(1).strip()

    m = re.match(r"^\d+\.\s+(.+?)\s+[A-Z]{1,3}$", line)
    if m:
        return m.group(1).strip()

    return re.sub(r"^\d+\.\s*", "", line).strip()


def parse_single_lineup_section(lines: list[str], label_idx: int) -> tuple[list[str], str, int, dict[str, Any]]:
    names: list[str] = []
    i = label_idx + 1
    diagnostics = {
        "first_nonempty_line_below_label": None,
        "numbered_rows_found": 0,
        "tbd_found": False,
        "section_stop_reason": None,
    }

    while i < len(lines):
        line = lines[i]

        if not diagnostics["first_nonempty_line_below_label"] and line:
            diagnostics["first_nonempty_line_below_label"] = line

        if is_lineup_label(line):
            diagnostics["section_stop_reason"] = "next_lineup_label"
            break

        if is_matchup_header(line):
            diagnostics["section_stop_reason"] = "next_matchup_header"
            break

        if line == "TBD":
            diagnostics["tbd_found"] = True
            diagnostics["section_stop_reason"] = "tbd"
            return [], "tbd", i + 1, diagnostics

        if is_batter_line(line):
            names.append(extract_batter_name_from_line(line))
            diagnostics["numbered_rows_found"] += 1

        i += 1

    if names:
        if diagnostics["section_stop_reason"] is None:
            diagnostics["section_stop_reason"] = "end_of_section_with_names"
        return names, "announced", i, diagnostics

    if diagnostics["section_stop_reason"] is None:
        diagnostics["section_stop_reason"] = "end_of_section_without_names"

    return [], "unknown", i, diagnostics


def find_first_two_lineup_labels_after_header(lines: list[str], start_idx: int) -> tuple[list[tuple[int, str]], dict[str, Any]]:
    labels: list[tuple[int, str]] = []
    i = start_idx + 1
    skipped_lines: list[str] = []

    while i < len(lines):
        line = lines[i]

        if is_matchup_header(line):
            return labels, {
                "stopped_on": "next_matchup_header",
                "skipped_sample": skipped_lines[:25],
                "skipped_count": len(skipped_lines),
            }

        if is_lineup_label(line):
            labels.append((i, line))
            if len(labels) == 2:
                return labels, {
                    "stopped_on": "second_lineup_label_found",
                    "skipped_sample": skipped_lines[:25],
                    "skipped_count": len(skipped_lines),
                }
        else:
            skipped_lines.append(line)

        i += 1

    return labels, {
        "stopped_on": "end_of_page",
        "skipped_sample": skipped_lines[:25],
        "skipped_count": len(skipped_lines),
    }


def parse_announced_lineups_from_page_text(page_text: str) -> list[dict[str, Any]]:
    raw_lines = [normalize_line(x) for x in page_text.splitlines()]
    lines = [x for x in raw_lines if x]

    games: list[dict[str, Any]] = []
    i = 0

    while i < len(lines):
        line = lines[i]

        if not is_matchup_header(line):
            i += 1
            continue

        parts = line.split(" @ ", 1)
        if len(parts) != 2:
            i += 1
            continue

        away_raw = parts[0].strip()
        home_raw = parts[1].strip()
        raw_matchup_header = line

        away_team = canonicalize_team_name_from_page(away_raw)
        home_team = canonicalize_team_name_from_page(home_raw)

        lineup_labels, header_diag = find_first_two_lineup_labels_after_header(lines, i)

        entry: dict[str, Any] = {
            "raw_matchup_header": raw_matchup_header,
            "away_team": away_team,
            "home_team": home_team,
            "away_lineup_names": [],
            "home_lineup_names": [],
            "away_lineup_status": "unknown",
            "home_lineup_status": "unknown",
            "failure_stage": None,
            "failure_detail": None,
            "header_diagnostics": header_diag,
        }

        if len(lineup_labels) == 0:
            entry["failure_stage"] = "no_lineup_labels_found"
            entry["failure_detail"] = (
                "No 'XXX Lineup' labels were found after the matchup header before the next matchup or end of page."
            )
            games.append(entry)
            i += 1
            continue

        if len(lineup_labels) == 1:
            entry["failure_stage"] = "only_one_lineup_label_found"
            entry["failure_detail"] = "Only one lineup label was found after the matchup header."
            entry["away_label"] = lineup_labels[0][1].replace(" Lineup", "").strip()
            games.append(entry)
            i += 1
            continue

        away_label_idx, away_label = lineup_labels[0]
        home_label_idx, home_label = lineup_labels[1]

        away_names, away_status, _, away_diag = parse_single_lineup_section(lines, away_label_idx)
        home_names, home_status, next_idx, home_diag = parse_single_lineup_section(lines, home_label_idx)

        entry.update(
            {
                "away_label": away_label.replace(" Lineup", "").strip(),
                "home_label": home_label.replace(" Lineup", "").strip(),
                "away_lineup_names": away_names,
                "home_lineup_names": home_names,
                "away_lineup_status": away_status,
                "home_lineup_status": home_status,
                "away_section_diagnostics": away_diag,
                "home_section_diagnostics": home_diag,
            }
        )

        if away_status == "unknown" and home_status == "unknown":
            entry["failure_stage"] = "lineup_sections_unreadable"
            entry["failure_detail"] = (
                "Both lineup labels were found, but neither section contained TBD nor readable numbered batter rows."
            )
        elif away_status == "unknown":
            entry["failure_stage"] = "away_lineup_section_unreadable"
            entry["failure_detail"] = (
                "Away lineup label was found, but section contained neither TBD nor readable numbered batter rows."
            )
        elif home_status == "unknown":
            entry["failure_stage"] = "home_lineup_section_unreadable"
            entry["failure_detail"] = (
                "Home lineup label was found, but section contained neither TBD nor readable numbered batter rows."
            )

        games.append(entry)
        i = next_idx

    return games


def extract_raw_matchup_title_from_node(matchup_node) -> str | None:
    away_node = matchup_node.select_one(".starting-lineups__team-name--away")
    at_node = matchup_node.select_one(".starting-lineups__team-name--at")
    home_node = matchup_node.select_one(".starting-lineups__team-name--home")

    away = away_node.get_text(" ", strip=True) if away_node else ""
    at = at_node.get_text(" ", strip=True) if at_node else "@"
    home = home_node.get_text(" ", strip=True) if home_node else ""

    if not away or not home:
        return None

    return re.sub(r"\s+", " ", f"{away} {at} {home}").strip()


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

    players: list[dict[str, str]] = []

    for li in player_items:
        player_link = li.select_one("a.starting-lineups__player--link")
        position_span = li.select_one("span.starting-lineups__player--position")

        name = player_link.get_text(" ", strip=True) if player_link else ""
        position = position_span.get_text(" ", strip=True) if position_span else "N/A"

        name = normalize_line(name)
        position = normalize_line(position)

        if name and name.upper() != "TBD":
            players.append(
                {
                    "name": name,
                    "position": position,
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


def extract_raw_matchup_titles_from_html(page_html: str) -> list[str]:
    soup = BeautifulSoup(page_html, "html.parser")
    titles: list[str] = []

    matchup_nodes = soup.select("div.starting-lineups__team-names")
    for matchup_node in matchup_nodes:
        raw_title = extract_raw_matchup_title_from_node(matchup_node)
        if raw_title:
            titles.append(raw_title)

    return titles


def build_mlb_title_lookup_from_html(page_html: str) -> dict[tuple[str, str], dict[str, Any]]:
    lookup: dict[tuple[str, str], dict[str, Any]] = {}

    for raw_title in extract_raw_matchup_titles_from_html(page_html):
        away_canon, home_canon = canonicalize_matchup_title(raw_title)
        if not away_canon or not home_canon:
            continue

        lookup[(away_canon, home_canon)] = {
            "raw_title": raw_title,
            "away_team": away_canon,
            "home_team": home_canon,
        }

    return lookup


def build_announced_lineups_lookup_from_html(page_html: str) -> dict[tuple[str, str], dict[str, Any]]:
    soup = BeautifulSoup(page_html, "html.parser")
    lookup: dict[tuple[str, str], dict[str, Any]] = {}

    matchup_nodes = soup.select("div.starting-lineups__team-names")

    for matchup_node in matchup_nodes:
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

        away_lineup = extract_team_players_from_ol(away_ol)
        home_lineup = extract_team_players_from_ol(home_ol)

        lookup[(away_canon, home_canon)] = {
            "raw_matchup_header": raw_title,
            "away_team": away_canon,
            "home_team": home_canon,
            "away_lineup": away_lineup,
            "home_lineup": home_lineup,
        }

    return lookup


def _expand_team_canonicals(canon: str) -> set[str]:
    """
    Return every canonical name that could represent the same team as `canon`.
    Walks TEAM_ALIAS_LOOKUP both directions so nicknames / abbreviations
    collapsed to the same canonical are all included.
    """
    alts: set[str] = {canon}
    # If canon is itself an alias key, grab its canonical
    resolved = TEAM_ALIAS_LOOKUP.get(canon)
    if resolved:
        alts.add(resolved)
    # Collect all aliases that point to the same canonical
    target = TEAM_ALIAS_LOOKUP.get(canon, canon)
    for norm, c in TEAM_ALIAS_LOOKUP.items():
        if c == target:
            alts.add(c)
            alts.add(norm)
    return {a for a in alts if a}


def _fuzzy_match_in_lookup(
    away_canon: str,
    home_canon: str,
    lookup: dict[tuple[str, str], Any],
) -> Optional[tuple[str, str]]:
    """
    Try every combination of alias expansions for (away_canon, home_canon)
    against the lookup keys. Returns the first matching key or None.
    """
    if (away_canon, home_canon) in lookup:
        return (away_canon, home_canon)

    away_alts = _expand_team_canonicals(away_canon)
    home_alts = _expand_team_canonicals(home_canon)

    for ak in away_alts:
        for hk in home_alts:
            if (ak, hk) in lookup:
                return (ak, hk)

    return None


def get_matching_mlb_title_for_full_game_title(
    full_game_title: str | None,
    mlb_title_lookup: dict[tuple[str, str], dict[str, Any]],
) -> dict[str, Any]:
    away_canon, home_canon = canonicalize_matchup_title(full_game_title)
    if not away_canon or not home_canon:
        return {
            "matched": False,
            "match_method": None,
            "reason": f"Could not split/canonicalize game title: {full_game_title!r}",
            "raw_mlb_title": None,
            "canonical_key": None,
            "candidates_checked": list(mlb_title_lookup.keys()),
        }

    # 1. Exact canonical key match.
    item = mlb_title_lookup.get((away_canon, home_canon))
    if item is not None:
        return {
            "matched": True,
            "match_method": "exact",
            "reason": None,
            "raw_mlb_title": item["raw_title"],
            "canonical_key": (away_canon, home_canon),
            "candidates_checked": [],
        }

    # 2. Fuzzy alias expansion fallback.
    fuzzy_key = _fuzzy_match_in_lookup(away_canon, home_canon, mlb_title_lookup)
    if fuzzy_key is not None:
        item = mlb_title_lookup[fuzzy_key]
        return {
            "matched": True,
            "match_method": "fuzzy_alias",
            "reason": None,
            "raw_mlb_title": item["raw_title"],
            "canonical_key": fuzzy_key,
            "candidates_checked": list(mlb_title_lookup.keys()),
        }

    return {
        "matched": False,
        "match_method": None,
        "reason": (
            f"No MLB page title matched {full_game_title!r}. "
            f"Searched canonical key: ({away_canon!r}, {home_canon!r}). "
            f"Page has {len(mlb_title_lookup)} entries."
        ),
        "raw_mlb_title": None,
        "canonical_key": (away_canon, home_canon),
        "candidates_checked": list(mlb_title_lookup.keys()),
    }


def print_raw_matchup_titles(title: str, matchup_titles: list[str], page_url: str | None = None) -> None:
    print("=" * 110)
    print(title)
    if page_url:
        print(f"Source page: {page_url}")

    if not matchup_titles:
        print("  No matchup titles parsed.")
        return

    for idx, matchup_title in enumerate(matchup_titles, start=1):
        print(f"{idx}. {matchup_title}")


def print_mlb_title_match_result(full_title: str, match_result: dict[str, Any]) -> None:
    print(f"Full game title: {full_title}")
    print(f"Matched: {match_result.get('matched')} | method: {match_result.get('match_method')}")
    print(f"Matched MLB page title: {match_result.get('raw_mlb_title')}")
    if match_result.get("canonical_key") is not None:
        print(f"Canonical key searched: {match_result['canonical_key']}")
    if match_result.get("reason"):
        print(f"Reason: {match_result['reason']}")
    candidates = match_result.get("candidates_checked") or []
    if candidates and not match_result.get("matched"):
        print(f"  Page canonical keys ({len(candidates)}):")
        for c in candidates:
            print(f"    {c}")


def _text_parser_game_to_lookup_entry(game_entry: dict[str, Any]) -> dict[str, Any]:
    """
    Convert a record from parse_announced_lineups_from_page_text() into the
    same dict shape that build_announced_lineups_lookup_from_html() produces,
    so both paths feed the same downstream code.
    """
    def names_to_lineup(names: list[str], status: str) -> dict[str, Any]:
        if status == "tbd":
            return {"status": "tbd", "reason": "Lineup TBD on MLB page.", "players": []}
        if not names:
            return {"status": "unknown", "reason": "No batter names extracted.", "players": []}
        return {
            "status": "announced",
            "reason": None,
            "players": [{"name": n, "position": "N/A"} for n in names],
        }

    return {
        "raw_matchup_header": game_entry.get("raw_matchup_header"),
        "away_team": game_entry.get("away_team"),
        "home_team": game_entry.get("home_team"),
        "away_lineup": names_to_lineup(
            game_entry.get("away_lineup_names", []),
            game_entry.get("away_lineup_status", "unknown"),
        ),
        "home_lineup": names_to_lineup(
            game_entry.get("home_lineup_names", []),
            game_entry.get("home_lineup_status", "unknown"),
        ),
    }


def build_announced_lineups_lookup(games: list[dict[str, Any]]) -> dict[tuple[str, str], dict[str, Any]]:
    pages_by_url: dict[str, str] = {}
    lookup: dict[tuple[str, str], dict[str, Any]] = {}

    for game in games:
        game_dt = game.get("parsed_game_datetime_utc")
        url = build_starting_lineups_url_from_game_dt(game_dt)

        if url not in pages_by_url:
            page_html, _, fetch_err = fetch_starting_lineups_page_html(game_dt)
            if page_html:
                pages_by_url[url] = page_html
            else:
                pages_by_url[url] = ""
                print(f"  [WARN] Failed to fetch {url}: {fetch_err}")

        page_html = pages_by_url[url]
        if not page_html:
            continue

        # --- Primary: CSS-selector HTML parser ---
        page_lookup = build_announced_lineups_lookup_from_html(page_html)

        if page_lookup:
            lookup.update(page_lookup)
            continue

        # --- Fallback: text-based parser (robust against HTML structure changes) ---
        print(f"  [INFO] HTML CSS selectors returned 0 matchups for {url}. Trying text parser.")
        print(f"  [DEBUG] First 1500 chars of raw HTML:")
        print(f"  {page_html[:1500]!r}")
        print()

        soup = BeautifulSoup(page_html, "html.parser")
        page_text = soup.get_text("\n", strip=True)
        text_games = parse_announced_lineups_from_page_text(page_text)

        for tg in text_games:
            away_canon = tg.get("away_team")
            home_canon = tg.get("home_team")
            if away_canon and home_canon:
                lookup[(away_canon, home_canon)] = _text_parser_game_to_lookup_entry(tg)

        if text_games:
            print(f"  [INFO] Text parser found {len(text_games)} matchup(s).")
        else:
            print(f"  [WARN] Text parser also found 0 matchups. Page may be JS-rendered or blocked.")

    return lookup


def get_announced_lineup_names_for_game(
    away_team: str | None,
    home_team: str | None,
    announced_lookup: dict[tuple[str, str], dict[str, Any]],
) -> dict[str, Any]:
    away_canon = canonicalize_team_name(away_team)
    home_canon = canonicalize_team_name(home_team)

    # 1. Exact canonical key.
    item = announced_lookup.get((away_canon, home_canon))
    match_method = "exact"

    # 2. Fuzzy alias expansion fallback.
    if item is None:
        fuzzy_key = _fuzzy_match_in_lookup(away_canon, home_canon, announced_lookup)
        if fuzzy_key is not None:
            item = announced_lookup[fuzzy_key]
            match_method = "fuzzy_alias"

    if item is not None:
        return {
            "source": "MLB starting lineups page HTML",
            "match_method": match_method,
            "reason": None,
            "diag_away_canon": away_canon,
            "diag_home_canon": home_canon,
            "diag_lookup_keys": list(announced_lookup.keys()),
            "raw_matchup_header": item.get("raw_matchup_header"),
            "away_lineup_status": item["away_lineup"]["status"],
            "home_lineup_status": item["home_lineup"]["status"],
            "away_lineup_reason": item["away_lineup"].get("reason"),
            "home_lineup_reason": item["home_lineup"].get("reason"),
            "away_lineup_players": item["away_lineup"].get("players", []),
            "home_lineup_players": item["home_lineup"].get("players", []),
        }

    return {
        "source": "MLB starting lineups page HTML",
        "match_method": None,
        "reason": (
            f"No MLB HTML lineup block matched scheduled game {away_team} @ {home_team}. "
            f"Searched key: ({away_canon!r}, {home_canon!r}). "
            f"Lookup has {len(announced_lookup)} entries."
        ),
        "diag_away_canon": away_canon,
        "diag_home_canon": home_canon,
        "diag_lookup_keys": list(announced_lookup.keys()),
        "raw_matchup_header": None,
        "away_lineup_status": "not_found",
        "home_lineup_status": "not_found",
        "away_lineup_reason": None,
        "home_lineup_reason": None,
        "away_lineup_players": [],
        "home_lineup_players": [],
    }


def print_metric_line(label: str, block: dict[str, Any]) -> None:
    value = block.get(f"{label} value", "N/A")
    source_key = block.get(f"{label} source_key")
    reason = block.get(f"{label} reason")

    print(f"  {label}: {value} | source_key: {source_key}")
    if reason:
        print(f"    Reason: {reason}")


def print_team_defensive_block(title: str, block: dict[str, Any]) -> None:
    print(title)
    print(f"  Source: {block.get('source')}")
    print(f"  Stat type: {block.get('stat_type')}")
    print(f"  Team row matched: {block.get('team_name_source')}")
    print(f"  Team ID: {block.get('team_id')}")
    print(f"  PutOuts: {block.get('putOuts')}")
    print(f"  Assists: {block.get('assists')}")
    print(f"  Errors: {block.get('errors')}")
    print(f"  Double Plays: {block.get('doublePlays')}")
    print(f"  Fielding %: {block.get('fielding')}")
    if block.get("reason"):
        print(f"  Reason: {block['reason']}")


def print_lineup_block(title: str, block: dict[str, Any]) -> None:
    print(title)
    print(f"  Source: {block.get('source')}")
    print(f"  Stat type: {block.get('stat_type')}")
    print(f"  Confirmed: {block.get('confirmed')}")
    if block.get("reason"):
        print(f"  Reason: {block['reason']}")

    for batter in block.get("batters", []):
        print(
            f"  {batter.get('batting_order')}. {batter.get('name', 'N/A')} ({batter.get('position', 'N/A')}) | "
            f"status: {batter.get('status', 'N/A')}"
        )


def print_lineup_failure_diagnostics(title: str, announced_names: dict[str, Any]) -> None:
    print(title)
    if announced_names.get("reason"):
        print(f"  Detail: {announced_names['reason']}")
    if announced_names.get("away_lineup_reason"):
        print(f"  Away detail: {announced_names['away_lineup_reason']}")
    if announced_names.get("home_lineup_reason"):
        print(f"  Home detail: {announced_names['home_lineup_reason']}")


def zscore(value, mean, std):
    if value is None or std in (None, 0):
        return None
    return (value - mean) / std


def weighted_mean_available(feature_dict, weights):
    used = []
    for key, weight in weights.items():
        value = feature_dict.get(key)
        if value is not None:
            used.append((value, weight))

    if not used:
        return 0.0, 0.0

    score = sum(v * w for v, w in used) / sum(w for _, w in used)
    confidence = sum(w for _, w in used) / sum(weights.values())
    return score, confidence


def build_lineup_offense_z_from_enriched_players(enriched_players, handedness_adj=0.0):
    """
    Fallback / secondary team offense score built ONLY from Savant-derived
    advanced stats already attached to enriched lineup players.

    This replaces the old MLB-live-feed-based build_lineup_offense_z().
    """

    if not enriched_players:
        return 0.0, 0.0

    def avg_adv_stat(stat_name):
        vals = [
            safe_float(p.get("advanced_stats", {}).get(stat_name))
            for p in enriched_players
        ]
        vals = [v for v in vals if v is not None]
        return sum(vals) / len(vals) if vals else None

    raw = {
        "OBP": avg_adv_stat("OBP"),
        "SLG": avg_adv_stat("SLG"),
        "BB%": avg_adv_stat("BB%"),
        "K%": avg_adv_stat("K%"),
        "ISO": avg_adv_stat("ISO"),
        "xwOBA": avg_adv_stat("xwOBA"),
    }

    # Missing-safe simple composite from Savant-only stats
    features = {
        "OBP": raw["OBP"],
        "SLG": raw["SLG"],
        "BB%": (raw["BB%"] / 100.0) if raw["BB%"] is not None else None,
        "K%_penalty": -(raw["K%"] / 100.0) if raw["K%"] is not None else None,
        "ISO": raw["ISO"],
        "xwOBA": raw["xwOBA"],
    }

    weights = {
        "OBP": 0.22,
        "SLG": 0.18,
        "BB%": 0.14,
        "K%_penalty": 0.12,
        "ISO": 0.14,
        "xwOBA": 0.20,
    }

    score, confidence = weighted_mean_available(features, weights)
    score += handedness_adj
    return score, confidence


def build_pitcher_z(pitcher_block, league_means, league_stds):
    raw = {
        "WHIP": safe_float(pitcher_block.get("WHIP value")),
        "AVG": safe_float(pitcher_block.get("AVG value")),
        "BB": safe_float(pitcher_block.get("BB value")),
        "HR": safe_float(pitcher_block.get("HR value")),
        "SO": safe_float(pitcher_block.get("SO value")),
    }

    z = {
        "WHIP_bad": -zscore(raw["WHIP"], league_means["WHIP"], league_stds["WHIP"]) if raw["WHIP"] is not None else None,
        "AVG_bad": -zscore(raw["AVG"], league_means["AVG"], league_stds["AVG"]) if raw["AVG"] is not None else None,
        "BB_bad": -zscore(raw["BB"], league_means["BB"], league_stds["BB"]) if raw["BB"] is not None else None,
        "HR_bad": -zscore(raw["HR"], league_means["HR"], league_stds["HR"]) if raw["HR"] is not None else None,
        "SO_good": zscore(raw["SO"], league_means["SO"], league_stds["SO"]) if raw["SO"] is not None else None,
    }

    weights = {
        "WHIP_bad": 0.35,
        "AVG_bad": 0.20,
        "BB_bad": 0.15,
        "HR_bad": 0.15,
        "SO_good": 0.15,
    }

    raw_score, raw_conf = weighted_mean_available(z, weights)

    # Pull score toward league mean (0) and shrink confidence proportionally
    # based on how many innings the pitcher has actually accumulated this season.
    reliability = safe_float(pitcher_block.get("reliability"), default=1.0)
    return raw_score * reliability, raw_conf * reliability


def build_defense_z(def_block, league_means, league_stds):
    fld_pct = safe_float(def_block.get("fielding"))
    errors = safe_float(def_block.get("errors"))
    double_plays = safe_float(def_block.get("doublePlays"))

    z = {
        "FldPct_good": zscore(fld_pct, league_means["FldPct"], league_stds["FldPct"]) if fld_pct is not None else None,
        "E_good": -zscore(errors, league_means["E"], league_stds["E"]) if errors is not None else None,
        "DP_good": zscore(double_plays, league_means["DP"], league_stds["DP"]) if double_plays is not None else None,
    }

    weights = {
        "FldPct_good": 0.50,
        "E_good": 0.30,
        "DP_good": 0.20,
    }

    return weighted_mean_available(z, weights)


def build_team_strength(off_score, pitch_score, def_score):
    return 0.50 * off_score + 0.30 * pitch_score + 0.20 * def_score


def build_competitiveness_score(team_a_strength, team_b_strength, k=0.7):
    gap = abs(team_a_strength - team_b_strength)
    return 100 * exp(-k * gap), gap


# ---------------------------------------------------------------------------
# Same-metric gap model helpers
# ---------------------------------------------------------------------------

def build_team_pitcher_metric_dict(pitcher_block: dict) -> dict[str, Optional[float]]:
    return {
        "WHIP": safe_float(pitcher_block.get("WHIP value")),
        "AVG_allowed": safe_float(pitcher_block.get("AVG value")),
        "BB": safe_float(pitcher_block.get("BB value")),
        "HR": safe_float(pitcher_block.get("HR value")),
        "SO": safe_float(pitcher_block.get("SO value")),
        "IP": safe_float(pitcher_block.get("inningsPitched_decimal")),
        "gamesPlayed": safe_float(pitcher_block.get("gamesPlayed")),
        "gamesStarted": safe_float(pitcher_block.get("gamesStarted")),
    }


def build_team_defense_metric_dict(def_block: dict) -> dict[str, Optional[float]]:
    return {
        "fielding": safe_float(def_block.get("fielding")),
        "errors": safe_float(def_block.get("errors")),
        "doublePlays": safe_float(def_block.get("doublePlays")),
        "putOuts": safe_float(def_block.get("putOuts")),
        "assists": safe_float(def_block.get("assists")),
    }


def build_team_offense_metric_dict(
    enriched_players: list[dict],
    lineup_summary: dict,
) -> dict[str, Optional[float]]:
    stat_names = [
        "OBP", "SLG", "OPS", "ISO", "xwOBA", "xBA", "xSLG",
        "BB%", "K%", "Barrel%", "HardHit%", "SweetSpot%", "AvgEV", "SprintSpeed",
    ]
    result: dict[str, Optional[float]] = {}
    for stat in stat_names:
        num, denom = 0.0, 0.0
        for p in enriched_players:
            v = safe_float(p.get("advanced_stats", {}).get(stat))
            if v is not None:
                w = p.get("lineup_spot_weight", 1.0)
                num += v * w
                denom += w
        result[stat] = num / denom if denom > 0 else None
    result["lineup_score"] = safe_float(lineup_summary.get("team_lineup_score")) if lineup_summary else None
    return result


def compute_same_metric_gaps(
    away_metrics: dict[str, Optional[float]],
    home_metrics: dict[str, Optional[float]],
    scales: dict[str, float],
) -> tuple[dict[str, float], dict[str, str], float]:
    """
    For each metric key present in both dicts, compute abs(away - home) / scale.
    Returns (gap_dict, skip_reasons, coverage_fraction).
    Coverage fraction = fraction of keys where both sides had data.
    """
    gaps: dict[str, float] = {}
    skip_reasons: dict[str, str] = {}
    all_keys = set(away_metrics) | set(home_metrics)

    for key in all_keys:
        a = safe_float(away_metrics.get(key))
        h = safe_float(home_metrics.get(key))
        if a is None or h is None:
            skip_reasons[key] = (
                f"away={'missing' if a is None else 'ok'}, "
                f"home={'missing' if h is None else 'ok'}"
            )
            continue
        scale = scales.get(key, 1.0)
        if scale <= 0:
            skip_reasons[key] = "scale <= 0"
            continue
        gaps[key] = abs(a - h) / scale

    total = len(all_keys)
    coverage = len(gaps) / total if total > 0 else 0.0
    return gaps, skip_reasons, coverage


def build_same_metric_gap_score(
    gaps: dict[str, float],
    weights: dict[str, float],
) -> tuple[float, float]:
    """
    Weighted mean of normalized gaps for a component.
    Returns (gap_score, coverage_fraction).
    Higher gap_score = more imbalanced = less competitive.
    """
    used = [(gaps[k], w) for k, w in weights.items() if k in gaps]
    if not used:
        return 0.0, 0.0
    score = sum(g * w for g, w in used) / sum(w for _, w in used)
    coverage = sum(w for _, w in used) / sum(weights.values())
    return score, coverage


def build_same_metric_competitiveness(
    pitcher_gap_score: float,
    offense_gap_score: float,
    defense_gap_score: float,
    k: float = 0.7,
) -> tuple[float, float]:
    """
    Combine component gap scores into a single competitiveness score [0, 100].
    Small total gap → high competitiveness (teams similar).
    Large total gap → low competitiveness (teams mismatched).
    """
    total_gap = (
        0.40 * pitcher_gap_score
        + 0.35 * offense_gap_score
        + 0.25 * defense_gap_score
    )
    return 100.0 * exp(-k * total_gap), total_gap


WIN_PROB_COEFFS_PATH = Path(__file__).resolve().parent / "win_prob_coefficients.json"


def load_win_prob_coefficients(path: Path) -> dict | None:
    """Load fitted logistic-regression coefficients, or None if not yet fitted."""
    if not path.exists():
        return None
    try:
        data = json.loads(path.read_text(encoding="utf-8"))
    except (json.JSONDecodeError, OSError):
        return None
    if not all(k in data for k in ("b0", "b1", "b2")):
        return None
    return data


def compute_win_probability(coeffs: dict | None,
                            signed_strength_gap: float,
                            smg_total_gap: float) -> float | None:
    """
    q = sigmoid(b0 + b1*signed_strength_gap + b2*smg_total_gap).
    Returns None if coefficients aren't available yet -- callers must treat a
    None q as 'not calibrated, do not bet', never as 0.5 or any default.
    """
    if coeffs is None:
        return None
    z = coeffs["b0"] + coeffs["b1"] * signed_strength_gap + coeffs["b2"] * smg_total_gap
    return 1.0 / (1.0 + exp(-z))


def load_existing_signal_record_game_ids(csv_path: Path) -> set[str]:
    if not csv_path.exists():
        return set()
    existing_ids = set()
    with csv_path.open("r", newline="", encoding="utf-8") as handle:
        for row in csv.DictReader(handle):
            game_id = row.get("game_id")
            if game_id:
                existing_ids.add(str(game_id))
    return existing_ids


def append_signal_record(csv_path: Path, record: dict) -> None:
    csv_path.parent.mkdir(parents=True, exist_ok=True)
    file_exists = csv_path.exists()
    with csv_path.open("a", newline="", encoding="utf-8") as handle:
        writer = csv.DictWriter(handle, fieldnames=SIGNAL_RECORD_FIELDNAMES)
        if not file_exists:
            writer.writeheader()
        writer.writerow(record)
        handle.flush()


def build_signal_record(
    game: dict,
    away_team: str,
    home_team: str,
    away_strength: float,
    home_strength: float,
    signed_strength_gap: float,
    strength_gap: float,
    competitiveness_score: float,
    smg_total_gap: float,
    smg_competitiveness: float,
    smg_confidence: float,
    overall_confidence: float,
) -> dict:
    """
    Pre-game signal snapshot only. away_score / home_score / away_won are
    intentionally left blank -- this file only ever processes games that
    haven't started yet, so the outcome can't be known at write time. A
    separate reconciliation step fills those columns in after the game
    finishes, matched on game_id.
    """
    return {
        "game_id": game.get("game_id"),
        "game_date": game.get("game_date"),
        "away_team": away_team,
        "home_team": home_team,
        "away_strength": round(away_strength, 6),
        "home_strength": round(home_strength, 6),
        "signed_strength_gap": round(signed_strength_gap, 6),
        "strength_gap": round(strength_gap, 6),
        "competitiveness_score": round(competitiveness_score, 4),
        "smg_total_gap": round(smg_total_gap, 6),
        "smg_competitiveness": round(smg_competitiveness, 4),
        "smg_confidence": round(smg_confidence, 4),
        "overall_confidence": round(overall_confidence, 4),
        "away_score": "",
        "home_score": "",
        "away_won": "",
    }


def print_enriched_announced_team_players(
    title: str,
    status: str,
    enriched_players: list[dict[str, Any]],
    lineup_summary: dict[str, Any],
    reason: str | None = None,
) -> None:
    print(title)
    print(f"  Status: {status}")

    if status == "tbd":
        print("  Lineup not announced yet (TBD).")
        if reason:
            print(f"  Reason: {reason}")
        return

    if status == "not_found":
        if reason:
            print(f"  Reason: {reason}")
        return

    # "live_feed" status: enriched players exist from live feed fallback — fall through to render.

    if not enriched_players:
        if reason:
            print(f"  Reason: {reason}")
        else:
            print("  No enriched lineup players available.")
        return

    for p in enriched_players:
        s = p["advanced_stats"]

        relevant_chunks = []
        if "G1_top_1_3" in p["groups"]:
            relevant_chunks.extend([
                f"OBP={fmt_stat(s.get('OBP'))}",
                f"BB%={fmt_stat(s.get('BB%'), 1)}",
                f"K%={fmt_stat(s.get('K%'), 1)}",
                f"SprintSpeed={fmt_stat(s.get('SprintSpeed'), 2)}",
            ])
        if "G2_mid_3_6" in p["groups"]:
            relevant_chunks.extend([
                f"ISO={fmt_stat(s.get('ISO'))}",
                f"SLG={fmt_stat(s.get('SLG'))}",
                f"xwOBA={fmt_stat(s.get('xwOBA'))}",
                f"xSLG={fmt_stat(s.get('xSLG'))}",
                f"Barrel%={fmt_stat(s.get('Barrel%'), 1)}",
                f"HardHit%={fmt_stat(s.get('HardHit%'), 1)}",
                f"AvgEV={fmt_stat(s.get('AvgEV'), 1)}",
                f"SweetSpot%={fmt_stat(s.get('SweetSpot%'), 1)}",
            ])
        if "G3_bot_7_9" in p["groups"]:
            relevant_chunks.extend([
                f"OPS={fmt_stat(s.get('OPS'), 1)}",
                f"OBP={fmt_stat(s.get('OBP'))}",
                f"K%={fmt_stat(s.get('K%'), 1)}",
                f"xBA={fmt_stat(s.get('xBA'))}",
            ])

        print(
            f"  {p['batting_order']}. {p['name']} | ({p['handedness']}) {p['position']} | "
            f"groups={','.join(p['groups'])} | "
            f"{' | '.join(relevant_chunks)} | "
            f"base_score={p['base_player_score']:.3f} | "
            f"spot_weight={p['lineup_spot_weight']:.2f} | "
            f"weighted_contribution={p['weighted_contribution']:.3f}"
        )

    print("  Group subtotals:")
    for group_name, subtotal in lineup_summary["group_subtotals"].items():
        print(f"    {group_name}: {subtotal:.3f}")

    print(f"  Final team lineup score: {lineup_summary['team_lineup_score']:.3f}")
    print(f"  Lineup score confidence: {lineup_summary['avg_confidence']:.2f}")


def main():
    now_utc = datetime.now(timezone.utc)
    window_end_utc = now_utc + timedelta(hours=LOOKAHEAD_HOURS)

    games = get_games_starting_within_next_hours(LOOKAHEAD_HOURS)
    existing_signal_game_ids = load_existing_signal_record_game_ids(SIGNAL_RECORDS_CSV_PATH)

    win_prob_coeffs = load_win_prob_coefficients(WIN_PROB_COEFFS_PATH)
    if win_prob_coeffs is None:
        print("[WIN PROB] No fitted coefficients found "
              f"({WIN_PROB_COEFFS_PATH.name}); q will be reported as N/A. "
              "Run win_probability_calibration.py first.")
    else:
        print(f"[WIN PROB] Loaded coefficients: "
              f"b0={win_prob_coeffs['b0']:+.4f} "
              f"b1={win_prob_coeffs['b1']:+.4f} "
              f"b2={win_prob_coeffs['b2']:+.4f}")
    print()

    print(f"Current UTC time: {now_utc.isoformat()}")
    print(f"Checking games starting until: {window_end_utc.isoformat()}")
    print()

    if not games:
        print(f"No MLB games starting within the next {LOOKAHEAD_HOURS} hours.")
        return

    first_game_dt = games[0].get("parsed_game_datetime_utc")
    page_html, page_url, page_reason = fetch_starting_lineups_page_html(first_game_dt)

    mlb_title_lookup: dict[tuple[str, str], dict[str, Any]] = {}

    if page_html is None:
        print("=" * 110)
        print("Parsed MLB page matchup titles:")
        print(f"Could not fetch MLB starting lineups page. Reason: {page_reason}")
        print()
    else:
        raw_matchup_titles = extract_raw_matchup_titles_from_html(page_html)
        print_raw_matchup_titles(
            "Parsed MLB page matchup titles:",
            raw_matchup_titles,
            page_url,
        )
        print()
        mlb_title_lookup = build_mlb_title_lookup_from_html(page_html)

    announced_lineups_lookup = build_announced_lineups_lookup(games)

    print("=" * 110)
    print("Announced lineups lookup diagnostics:")
    if not announced_lineups_lookup:
        print("  [WARN] Lookup is EMPTY — HTML parsing found no matchup blocks.")
        print("         Likely cause: MLB.com changed page structure; CSS selectors no longer match.")
    else:
        print(f"  {len(announced_lineups_lookup)} matchup(s) found in HTML lookup:")
        for k in announced_lineups_lookup:
            print(f"    key: {k}")
    print()

    # Warm the Savant cache once per run.
    _ = fetch_savant_custom_batting_table(SEASON)

    for i, game in enumerate(games, start=1):
        away_team = game.get("away_name")
        home_team = game.get("home_name")
        game_id = game.get("game_id")
        status = game.get("status")
        game_dt = game.get("parsed_game_datetime_utc")

        full_game_title = f"{away_team} @ {home_team}"
        title_match = get_matching_mlb_title_for_full_game_title(full_game_title, mlb_title_lookup)

        away_pitcher = game.get("away_probable_pitcher")
        home_pitcher = game.get("home_probable_pitcher")

        away_stats = get_pitcher_metric_block(away_pitcher, SEASON)
        home_stats = get_pitcher_metric_block(home_pitcher, SEASON)

        away_team_defense = get_team_defensive_block(away_team, SEASON)
        home_team_defense = get_team_defensive_block(home_team, SEASON)

        lineups = get_game_lineups(int(game_id))
        away_live_id_lookup = build_live_lineup_player_id_lookup(lineups["away"])
        home_live_id_lookup = build_live_lineup_player_id_lookup(lineups["home"])

        announced_names = get_announced_lineup_names_for_game(
            away_team,
            home_team,
            announced_lineups_lookup,
        )
        if announced_names["away_lineup_status"] == "not_found":
            away_key = canonicalize_team_name(away_team)
            home_key = canonicalize_team_name(home_team)
            print(f"  [DIAG] Lookup key searched: ({away_key!r}, {home_key!r})")
            print(f"  [DIAG] Keys in lookup: {list(announced_lineups_lookup.keys())}")


        advanced_away_lineup_score = 0.0
        advanced_home_lineup_score = 0.0
        advanced_away_lineup_conf = 0.0
        advanced_home_lineup_conf = 0.0

        away_pitch_score, away_pitch_conf = build_pitcher_z(away_stats, league_means, league_stds)
        home_pitch_score, home_pitch_conf = build_pitcher_z(home_stats, league_means, league_stds)

        away_def_score, away_def_conf = build_defense_z(away_team_defense, league_means, league_stds)
        home_def_score, home_def_conf = build_defense_z(home_team_defense, league_means, league_stds)

        # Resolve lineup player list: prefer HTML-parsed announced lineup,
        # fall back to live feed batting order when HTML page is unavailable (e.g. 403).
        def _live_feed_to_player_list(lineup_block: dict) -> list[dict[str, str]]:
            if not lineup_block.get("confirmed"):
                return []
            return [
                {"name": b["name"], "position": b.get("position", "N/A")}
                for b in lineup_block.get("batters", [])
                if b.get("name") and b["name"] != "N/A"
            ]

        away_lineup_players = announced_names.get("away_lineup_players") or []
        away_lineup_source = "html"
        if not away_lineup_players:
            away_lineup_players = _live_feed_to_player_list(lineups["away"])
            away_lineup_source = "live_feed" if away_lineup_players else "none"

        home_lineup_players = announced_names.get("home_lineup_players") or []
        home_lineup_source = "html"
        if not home_lineup_players:
            home_lineup_players = _live_feed_to_player_list(lineups["home"])
            home_lineup_source = "live_feed" if home_lineup_players else "none"

        if away_lineup_source == "live_feed":
            print(f"  [INFO] Away lineup sourced from live feed (HTML page unavailable).")
        if home_lineup_source == "live_feed":
            print(f"  [INFO] Home lineup sourced from live feed (HTML page unavailable).")

        away_enriched_players = []
        away_lineup_segment_summary = {"team_lineup_score": 0.0, "avg_confidence": 0.0, "group_subtotals": {}}
        if away_lineup_players:
            away_enriched_players = enrich_announced_team_players_with_lineup_scores(
                away_lineup_players,
                SEASON,
                team_name=away_team,
                live_player_id_lookup=away_live_id_lookup,
            )
            away_lineup_segment_summary = build_team_lineup_segment_score(away_enriched_players)

        home_enriched_players = []
        home_lineup_segment_summary = {"team_lineup_score": 0.0, "avg_confidence": 0.0, "group_subtotals": {}}
        if home_lineup_players:
            home_enriched_players = enrich_announced_team_players_with_lineup_scores(
                home_lineup_players,
                SEASON,
                team_name=home_team,
                live_player_id_lookup=home_live_id_lookup,
            )
            home_lineup_segment_summary = build_team_lineup_segment_score(home_enriched_players)

        away_off_score, away_off_conf = build_lineup_offense_z_from_enriched_players(away_enriched_players)
        home_off_score, home_off_conf = build_lineup_offense_z_from_enriched_players(home_enriched_players)

        away_off_score, away_off_conf = 0.0, 0.0
        home_off_score, home_off_conf = 0.0, 0.0

        if away_enriched_players:
            away_off_score, away_off_conf = build_lineup_offense_z_from_enriched_players(away_enriched_players)

        if home_enriched_players:
            home_off_score, home_off_conf = build_lineup_offense_z_from_enriched_players(home_enriched_players)

        if away_enriched_players:
            advanced_away_lineup_score = away_lineup_segment_summary["team_lineup_score"]
            advanced_away_lineup_conf = away_lineup_segment_summary["avg_confidence"]

        if home_enriched_players:
            advanced_home_lineup_score = home_lineup_segment_summary["team_lineup_score"]
            advanced_home_lineup_conf = home_lineup_segment_summary["avg_confidence"]

        final_away_off_score = away_off_score
        final_home_off_score = home_off_score
        final_away_off_conf = away_off_conf
        final_home_off_conf = home_off_conf

        if away_enriched_players:
            final_away_off_score = advanced_away_lineup_score
            final_away_off_conf = advanced_away_lineup_conf

        if home_enriched_players:
            final_home_off_score = advanced_home_lineup_score
            final_home_off_conf = advanced_home_lineup_conf

        away_strength = build_team_strength(final_away_off_score, away_pitch_score, away_def_score)
        home_strength = build_team_strength(final_home_off_score, home_pitch_score, home_def_score)

        competitiveness_score, strength_gap = build_competitiveness_score(away_strength, home_strength)
        signed_strength_gap = away_strength - home_strength  # positive = away favored

        overall_confidence = (
            final_away_off_conf + final_home_off_conf +
            away_pitch_conf + home_pitch_conf +
            away_def_conf + home_def_conf
        ) / 6.0

        minutes_to_start = int((game_dt - now_utc).total_seconds() // 60) if game_dt else None

        print("=" * 110)
        print(f"Game {i}: {away_team} @ {home_team}")
        print(f"Game ID: {game_id}")
        print(f"Status: {status}")
        print(f"Start time UTC: {game_dt.isoformat() if game_dt else 'Unknown'}")
        print(f"Minutes until start: {minutes_to_start}")
        print()

        print("MLB title correspondence:")
        print_mlb_title_match_result(full_game_title, title_match)
        print()

        print("Away probable pitcher:")
        print(f"  Pitcher: {away_stats['pitcher']} | player_id: {away_stats['player_id']}")
        if away_stats.get("global_reason"):
            print(f"  Global reason: {away_stats['global_reason']}")
        print_metric_line("HR", away_stats)
        print_metric_line("SO", away_stats)
        print_metric_line("AVG", away_stats)
        print_metric_line("BB", away_stats)
        print_metric_line("WHIP", away_stats)
        print(f"  Games played: {away_stats.get('gamesPlayed')} | Games started: {away_stats.get('gamesStarted')}")
        print(f"  IP (raw): {away_stats.get('inningsPitched')} | IP (decimal): {fmt_stat(away_stats.get('inningsPitched_decimal'), 1)}")
        print(f"  Reliability factor: {fmt_stat(away_stats.get('reliability'), 3)}")
        print()

        print("Home probable pitcher:")
        print(f"  Pitcher: {home_stats['pitcher']} | player_id: {home_stats['player_id']}")
        if home_stats.get("global_reason"):
            print(f"  Global reason: {home_stats['global_reason']}")
        print_metric_line("HR", home_stats)
        print_metric_line("SO", home_stats)
        print_metric_line("AVG", home_stats)
        print_metric_line("BB", home_stats)
        print_metric_line("WHIP", home_stats)
        print(f"  Games played: {home_stats.get('gamesPlayed')} | Games started: {home_stats.get('gamesStarted')}")
        print(f"  IP (raw): {home_stats.get('inningsPitched')} | IP (decimal): {fmt_stat(home_stats.get('inningsPitched_decimal'), 1)}")
        print(f"  Reliability factor: {fmt_stat(home_stats.get('reliability'), 3)}")
        print()

        print_team_defensive_block("Away team defensive stats:", away_team_defense)
        print()
        print_team_defensive_block("Home team defensive stats:", home_team_defense)
        print()

        print(f"Matched MLB website title: {announced_names.get('raw_matchup_header')}")
        print()

        # When HTML page was unavailable, enriched_players came from live feed.
        # Override status so print function renders stats instead of bailing early.
        def _effective_lineup_status(announced_status: str, enriched: list, source: str) -> str:
            if enriched:
                return "announced" if source == "html" else "live_feed"
            return announced_status

        away_print_status = _effective_lineup_status(
            announced_names["away_lineup_status"], away_enriched_players, away_lineup_source
        )
        home_print_status = _effective_lineup_status(
            announced_names["home_lineup_status"], home_enriched_players, home_lineup_source
        )

        print_enriched_announced_team_players(
            "Away lineup players (source: {}):" .format(away_lineup_source),
            away_print_status,
            away_enriched_players,
            away_lineup_segment_summary,
            announced_names.get("away_lineup_reason") or announced_names.get("reason"),
        )
        print()

        print_enriched_announced_team_players(
            "Home lineup players (source: {}):".format(home_lineup_source),
            home_print_status,
            home_enriched_players,
            home_lineup_segment_summary,
            announced_names.get("home_lineup_reason") or announced_names.get("reason"),
        )
        print()

        if (
            announced_names["away_lineup_status"] in {"unknown", "not_found"}
            or announced_names["home_lineup_status"] in {"unknown", "not_found"}
        ):
            print_lineup_failure_diagnostics("Lineup identification diagnostics:", announced_names)
            print()

        print_lineup_block("Away batting lineup from live feed:", lineups["away"])
        print()
        print_lineup_block("Home batting lineup from live feed:", lineups["home"])
        print()

        print("Competitiveness model:")
        print(f"  Away offense score used: {final_away_off_score:.3f} | confidence: {final_away_off_conf:.2f}")
        print(f"  Home offense score used: {final_home_off_score:.3f} | confidence: {final_home_off_conf:.2f}")
        print(f"  Away pitcher score: {away_pitch_score:.3f} | confidence: {away_pitch_conf:.2f}")
        print(f"  Home pitcher score: {home_pitch_score:.3f} | confidence: {home_pitch_conf:.2f}")
        print(f"  Away defense score: {away_def_score:.3f} | confidence: {away_def_conf:.2f}")
        print(f"  Home defense score: {home_def_score:.3f} | confidence: {home_def_conf:.2f}")
        print(f"  Away team strength: {away_strength:.3f}")
        print(f"  Home team strength: {home_strength:.3f}")
        print(f"  Strength gap: {strength_gap:.3f}")
        print(f"  Competitiveness score: {competitiveness_score:.2f} / 100")
        print(f"  Overall confidence: {overall_confidence:.2f}")
        print()

        print("Advanced announced-lineup model:")
        print(f"  Away advanced lineup score: {advanced_away_lineup_score:.3f} | confidence: {advanced_away_lineup_conf:.2f}")
        print(f"  Home advanced lineup score: {advanced_home_lineup_score:.3f} | confidence: {advanced_home_lineup_conf:.2f}")
        print()

        # -----------------------------------------------------------------------
        # Same-metric gap competitiveness model
        # -----------------------------------------------------------------------
        away_pitcher_metrics = build_team_pitcher_metric_dict(away_stats)
        home_pitcher_metrics = build_team_pitcher_metric_dict(home_stats)

        away_defense_metrics = build_team_defense_metric_dict(away_team_defense)
        home_defense_metrics = build_team_defense_metric_dict(home_team_defense)

        away_offense_metrics = build_team_offense_metric_dict(
            away_enriched_players, away_lineup_segment_summary
        )
        home_offense_metrics = build_team_offense_metric_dict(
            home_enriched_players, home_lineup_segment_summary
        )

        pitcher_gaps, pitcher_skip, pitcher_cov = compute_same_metric_gaps(
            away_pitcher_metrics, home_pitcher_metrics, METRIC_COMPARISON_SCALES
        )
        defense_gaps, defense_skip, defense_cov = compute_same_metric_gaps(
            away_defense_metrics, home_defense_metrics, METRIC_COMPARISON_SCALES
        )
        offense_gaps, offense_skip, offense_cov = compute_same_metric_gaps(
            away_offense_metrics, home_offense_metrics, METRIC_COMPARISON_SCALES
        )

        pitcher_gap_score, pitcher_gap_cov = build_same_metric_gap_score(pitcher_gaps, PITCHER_GAP_WEIGHTS)
        defense_gap_score, defense_gap_cov = build_same_metric_gap_score(defense_gaps, DEFENSE_GAP_WEIGHTS)
        offense_gap_score, offense_gap_cov = build_same_metric_gap_score(offense_gaps, OFFENSE_GAP_WEIGHTS)

        smg_competitiveness, smg_total_gap = build_same_metric_competitiveness(
            pitcher_gap_score, offense_gap_score, defense_gap_score
        )
        smg_confidence = (pitcher_gap_cov + offense_gap_cov + defense_gap_cov) / 3.0

        print("Same-metric gap competitiveness model:")
        print(f"  (Small normalized gap = teams similar = more competitive)")
        print()

        print("  Pitcher gaps:")
        for metric, gap in sorted(pitcher_gaps.items()):
            away_val = away_pitcher_metrics.get(metric)
            home_val = home_pitcher_metrics.get(metric)
            print(
                f"    {metric}: away={fmt_stat(away_val, 3)} | home={fmt_stat(home_val, 3)}"
                f" | norm_gap={gap:.3f}"
            )
        for metric, reason in sorted(pitcher_skip.items()):
            print(f"    {metric}: SKIPPED ({reason})")
        print(f"  Pitcher gap score: {pitcher_gap_score:.3f} | coverage: {pitcher_gap_cov:.2f}")
        print()

        print("  Defense gaps:")
        for metric, gap in sorted(defense_gaps.items()):
            away_val = away_defense_metrics.get(metric)
            home_val = home_defense_metrics.get(metric)
            print(
                f"    {metric}: away={fmt_stat(away_val, 3)} | home={fmt_stat(home_val, 3)}"
                f" | norm_gap={gap:.3f}"
            )
        for metric, reason in sorted(defense_skip.items()):
            print(f"    {metric}: SKIPPED ({reason})")
        print(f"  Defense gap score: {defense_gap_score:.3f} | coverage: {defense_gap_cov:.2f}")
        print()

        print("  Offense gaps:")
        for metric, gap in sorted(offense_gaps.items()):
            away_val = away_offense_metrics.get(metric)
            home_val = home_offense_metrics.get(metric)
            print(
                f"    {metric}: away={fmt_stat(away_val, 3)} | home={fmt_stat(home_val, 3)}"
                f" | norm_gap={gap:.3f}"
            )
        for metric, reason in sorted(offense_skip.items()):
            print(f"    {metric}: SKIPPED ({reason})")
        print(f"  Offense gap score: {offense_gap_score:.3f} | coverage: {offense_gap_cov:.2f}")
        print()

        print(f"  Pitcher gap score:  {pitcher_gap_score:.3f} (weight 0.40)")
        print(f"  Offense gap score:  {offense_gap_score:.3f} (weight 0.35)")
        print(f"  Defense gap score:  {defense_gap_score:.3f} (weight 0.25)")
        print(f"  Total same-metric gap: {smg_total_gap:.3f}")
        print(f"  SMG competitiveness score: {smg_competitiveness:.2f} / 100")
        print(f"  SMG model confidence: {smg_confidence:.2f}")
        print()

        q_away_win = compute_win_probability(
            win_prob_coeffs, signed_strength_gap, smg_total_gap
        )
        print("Model win probability:")
        if q_away_win is None:
            print("  q (P away win): N/A  -- coefficients not fitted yet")
        else:
            print(f"  q (P away win): {q_away_win:.4f}")
            print(f"  q (P home win): {1.0 - q_away_win:.4f}")
        print()

        if str(game_id) not in existing_signal_game_ids:
            signal_record = build_signal_record(
                game=game,
                away_team=away_team,
                home_team=home_team,
                away_strength=away_strength,
                home_strength=home_strength,
                signed_strength_gap=signed_strength_gap,
                strength_gap=strength_gap,
                competitiveness_score=competitiveness_score,
                smg_total_gap=smg_total_gap,
                smg_competitiveness=smg_competitiveness,
                smg_confidence=smg_confidence,
                overall_confidence=overall_confidence,
            )
            append_signal_record(SIGNAL_RECORDS_CSV_PATH, signal_record)
            existing_signal_game_ids.add(str(game_id))
            print(f"[SIGNAL RECORD] Logged game {game_id} ({away_team} @ {home_team}) "
                  f"-> {SIGNAL_RECORDS_CSV_PATH}")
        else:
            print(f"[SIGNAL RECORD] Game {game_id} already logged, skipping duplicate write.")
        print()


if __name__ == "__main__":
    main()