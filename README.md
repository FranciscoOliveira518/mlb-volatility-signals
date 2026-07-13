# mlb-quant-signals

![Python](https://img.shields.io/badge/python-3.9%2B-blue)

Pre-game quantitative signals for MLB games. Two standalone Python modules that pull
public data (MLB Stats API, Baseball Savant / Statcast), compute team-strength and
pitch-level volatility features, and write labeled records for win-probability
calibration and edge analysis. Each script runs independently and shares no imports.

## Strategy

The two modules work together to analyse the daily lineup of MLB games: those that are
both (a) closely matched at the team level and (b) likely to produce large, two-sided
scoring swings during play. Games meeting both conditions are the ones most likely to
see the in-game lead change hands.

Why that matters: the target play is temporal (legged) arbitrage on a binary prediction
market (which team loses and which wins). You take an underdog position pre-game at a
low price; then, if the game swings and the underdog moves in front, you complete a
second leg on the other side - now also cheap. If the two legs together cost less than
the $1.00 the winning side pays out, the position is locked and returns a profit
regardless of the final result.

The key point is that this locked, result-independent state is not guaranteed, meaning
it only becomes available if the game actually swings. This is therefore a bet on
realized volatility and that it is not priced in by the influence of the market makers
in the odds. It is not a classical arbitrage: if the swing never comes, no second leg
opens and the position simply resolves on the game's outcome. The purpose of the two
modules is to place that volatility bet only on the games where the swing is most
probable.

### How is competitiveness predicted?

Each team's overall strength is built from multiple season-to-date statistics on
offense, pitching, and defense, each converted to a league-relative z-score and combined
into a single weighted composite. The gap between the two teams' composites is passed
through a decay function, so evenly matched teams (small gap) score high and mismatches
score low. High competitiveness means the game is likely to stay close enough for the
lead to change hands. (Formulas in [How it works](#how-it-works).)

### How is two-sided volatility predicted?

The second module works at the pitch level. It builds each pitcher's pitch-type profile
from Statcast, matches it against every batter in the opposing lineup, and aggregates
those matchups into a game-level burst score - weighting lineup slots with the top of
the order heaviest. A high score means both offenses are capable of sudden scoring
bursts, meaning the game can swing in either direction. In addition to the burst score,
the pitcher and batter stats are also used to compute three other relevant scores to
enable an informed entry decision in a market: `two_sided_volatility_score`,
`one_sided_shock_score`, and `signed_run_assault_gap`.

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

**Team strength** (`limao.py`) - offense, pitching, and defense are converted to
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

**Volatility engine** (`Run_Assault…`) - builds per-pitcher pitch-type strength from
Statcast, matches it against each batter, and derives half-inning volatility segments,
run-assault risk, burst probability, collapse exposure, escape coverage, and
lineup-cluster risk. Lineup slots are weighted with the top of the order heaviest.

### Variables behind each score

Team strength (above) is a weighted composite of three league-relative z-scores; the
volatility and edge scores come from the second module, all built on a per-team
`run_assault_risk`. The table below summarises the main variables behind each quantity.

| Quantity | What it captures | Key inputs (coefficient) |
| --- | --- | --- |
| `offense_z` | Lineup's run-creation ability | OBP (0.22), xwOBA (0.20), SLG (0.18), ISO (0.14), BB% (0.14), K% penalty (0.12) |
| `pitching_z` | Probable starter's run prevention | WHIP (0.35), AVG (0.20), BB (0.15), HR (0.15), SO (0.15) — all lower-is-better except SO; scaled by innings reliability |
| `defense_z` | Team fielding | Fielding % (0.50), errors (0.30), double plays (0.20) |
| `run_assault_risk` (per team) | One offense's in-game burst threat vs the opposing pitcher | `50 + 0.45·lineup_pressure + 0.25·top-3 cluster + 0.15·top-4 cluster + 0.20·collapse_exposure − 0.10·escape_coverage` |
| Burst score (`p_at_least_one_burst`) | Probability of ≥1 big scoring burst in the game | per-half-inning `extension_risk` (0.40) + `run_conversion_risk` (0.35) + `p_6plus` (0.15) + lineup turnover (0.10) |
| `two_sided_volatility_score` | Both offenses can burst → lead can reverse | `0.70·min(away, home) + 0.20·avg − 0.25·asymmetry` over `run_assault_risk` |
| `one_sided_shock_score` | Only one offense can burst → swing won't reverse | `0.70·max(away, home) + 0.20·avg + 0.10·asymmetry` over `run_assault_risk` |
| `signed_run_assault_gap` | Which side carries the greater offensive threat | `away_run_assault_risk − home_run_assault_risk` (directional) |

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

- **MLB Stats API** - schedule, probable pitchers, live feed, team fielding.
- **Baseball Savant / Statcast** (`pybaseball` + custom leaderboard) - hitter metrics
  and pitch-level data.
- **mlb.com/starting-lineups** - announced lineups.

All sources are public and unauthenticated; no API keys are stored in these files.

## Notes

- `data/` output and the `pybaseball` cache are git-ignored.
- `Run_Assault__Pitcher-Batter_Analysis_.py` is meant to be run directly, not imported.
- These modules produce features and signals only - they do not place trades.

