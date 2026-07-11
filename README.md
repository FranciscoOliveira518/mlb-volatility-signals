# mlb-quant-signals

![Python](https://img.shields.io/badge/python-3.9%2B-blue)

Pre-game quantitative signals for MLB games. Two standalone Python modules that pull
public data (MLB Stats API, Baseball Savant / Statcast), compute team-strength and
pitch-level volatility features, and write labeled records for win-probability
calibration and edge analysis. Each script runs independently and shares no imports.

## Modules

| File | Role | Output |
| --- | --- | --- |
| `limao.py` | Live pre-game team-strength scanner | `data/signal_records.csv` |
| `Run_Assault__Pitcher-Batter_Analysis_.py` | Pitcher–batter matchup & volatility engine | `data/` (pitch strengths, matchups, volatility face-offs) |

## Installation

Requires **Python 3.9+** (3.11+ recommended).

```bash
pip install requests MLB-StatsAPI pandas beautifulsoup4 lxml pybaseball
```

On Windows, if TLS verification fails against Statcast endpoints, install `truststore`
to use the native Windows certificate store.

## Usage

### `limao.py`

Scans games starting within the next `LOOKAHEAD_HOURS` (default 10) and appends one
signal record per game. Takes no arguments; edit `SEASON` and `LOOKAHEAD_HOURS` at the
top of the file.

```bash
python limao.py
```

### `Run_Assault__Pitcher-Batter_Analysis_.py`

```bash
# Analyze a specific date
python "Run_Assault__Pitcher-Batter_Analysis_.py" --date 2026-07-11

# Or use the lookahead/lookback window around now
python "Run_Assault__Pitcher-Batter_Analysis_.py"
```

| Argument | Default | Description |
| --- | --- | --- |
| `--date` | — | Game date `YYYY-MM-DD`. If omitted, uses the lookahead window. |
| `--start-date` | season start | Statcast history start date `YYYY-MM-DD`. |
| `--lookahead-hours` | 10 | Hours ahead to include. |
| `--lookback-hours` | 2 | Hours behind to include. |

## How it works

**Team strength** (`limao.py`) — offense, pitching, and defense are converted to
league-relative z-scores and combined:

```
team_strength       = 0.50·offense_z + 0.30·pitching_z + 0.20·defense_z
signed_strength_gap = away_strength − home_strength
competitiveness     = 100 · exp(−0.7 · |gap|)
```

Win probability is computed only when fitted coefficients (`win_prob_coefficients.json`)
are present:

```
q = sigmoid(b0 + b1·signed_strength_gap + b2·smg_total_gap)
```

Without coefficients, `q` is reported as `N/A` (not 0.5).

**Volatility engine** (`Run_Assault…`) — builds per-pitcher pitch-type strength from
Statcast, matches it against each batter, and derives half-inning volatility segments,
run-assault risk, burst probability, collapse exposure, escape coverage, and
lineup-cluster risk. Lineup slots are weighted with the top of the order heaviest.

## Output

Both scripts create a local `data/` directory on first run:

```
data/
├── signal_records.csv                         # limao.py
├── pitcher_pitch_strength_latest.{csv,json}   # Run Assault
├── batter_pitch_strengths/                    # per-game strengths & matchups
└── volatility_faceoffs/                       # per-game face-offs, cluster risk, etc.
```

## Data sources

- **MLB Stats API** — schedule, probable pitchers, live feed, team fielding.
- **Baseball Savant / Statcast** (`pybaseball` + custom leaderboard) — hitter metrics
  and pitch-level data.
- **mlb.com/starting-lineups** — announced lineups.

All sources are public and unauthenticated; no API keys are stored in these files.

## Notes

- `data/` output and the `pybaseball` cache are git-ignored.
- `Run_Assault__Pitcher-Batter_Analysis_.py` is meant to be run directly, not imported.
- These modules produce features and signals only — they do not place trades.

## License

Add a `LICENSE` file if you intend to share this publicly (e.g. MIT).
