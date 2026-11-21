# Vendored / pinned dependencies

- `brownian-motion/` — **Lake path dependency**. Copy of lyasoff2016’s pruned
  pin (not upstream `RemyDegenne/brownian-motion` tip): unfinished decls that
  leave `sorry` in the Lyasoff build closure were dropped there so Palomar /
  clean builds are not poisoned by unused BM holes. Import modules selectively
  (as lyasoff2016 does); do **not** `lake build BrownianMotion` as an umbrella —
  some StochasticIntegral files still reference removed decls.
- `formal-mathfin/` — **Lake path dependency**. Pin matching lyasoff2016
  (Itô / Girsanov / MR / SDE / NFLVR scaffolding).
- `Stochastic-Process-lean-lib/` — **parked** (Lean 4.33). Semimartingale /
  Novikov / Girsanov depth if MathFin’s Novikov hole blocks us; not on the
  Lake graph until toolchain-aligned.
- `LeanRoughPaths/` — **parked** (Lean 4.35.0-rc3). Signature / shuffle /
  rough-path algebra; not on the Lake graph until toolchain-aligned.
- `palomar-policy/` — editorial policy pin (unchanged).

Prune parked trees later if unused. Pins and upstream SHAs: `SOURCES`.
