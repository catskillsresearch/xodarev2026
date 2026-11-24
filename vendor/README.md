# Vendored / pinned dependencies

- `brownian-motion/` — **Lake path dependency**. Copy of lyasoff2016’s pruned
  pin (not upstream `RemyDegenne/brownian-motion` tip): unfinished decls that
  leave `sorry` in the Lyasoff build closure were dropped there so Palomar /
  clean builds are not poisoned by unused BM holes. Import modules selectively
  (as lyasoff2016 does); do **not** `lake build BrownianMotion` as an umbrella —
  some StochasticIntegral files still reference removed decls.
- `formal-mathfin/` — **Lake path dependency**. Pin matching lyasoff2016
  (Itô / Girsanov / MR / SDE / NFLVR scaffolding). Only the `MathFin` library
  is kept (lakefile.toml); non-module upstream extras were removed (see `SOURCES`).
- `palomar-policy/` — editorial policy pin (unchanged).

The parked Stochastic-Process-lean-lib and LeanRoughPaths copies were removed
(unused). Pins and upstream SHAs: `SOURCES`.
