# Counterexample narratives

There is one short file per refuted paper claim. Each says what the counterexample is and why it
breaks the claim, and matches exactly what the Lean `not_X` theorem proves. These summaries are
the ones quoted in the official project description and the comparator notes.

| Paper claim | Lean | Narrative |
|---|---|---|
| Thm 4.2(ii) `←`, the iff, Theorem B | `not_affine_riccati_duality_mpr`, `not_affine_riccati_duality`, `not_theorem_B_mpr`, `not_theorem_B` (compared as `…_unwrapped`) | [affine_riccati_duality_mpr.md](affine_riccati_duality_mpr.md) |
| Unconditional completeness iff (not Thm 56's finite-polynomial subcase) | `not_theorem_C_unwrapped` (compared); `not_theorem_C`, `theorem_C_refuted` | [theorem_C.md](theorem_C.md) |
| Proposition 58 | `not_prop58_blackScholes_depth_zero` | [prop58.md](prop58.md) |
| Theorem D residual hypothesis | `theorem_D_residual_hypothesis_fails` (compared as `…_unwrapped`) | [theorem_D_residual.md](theorem_D_residual.md) |
| Lemma 77 (B.1) | `not_lemma77_shuffle_estimate`, `not_lemma77_of_hypH2` | [lemma77.md](lemma77.md) |
| Lemma 78 (B.2) | `not_lemma78_local_lipschitz` | [lemma78.md](lemma78.md) |
| Literal NFLVR (Defs 2.17+4.3) and terminal-only bound (Sec. 4.6) | `not_literal_nflvr_unwrapped`, `not_terminal_bdd_nflvr_unwrapped` (compared); library `not_literal_nflvr`, `not_terminal_bdd_nflvr` | [nflvr_literal.md](nflvr_literal.md) |

## Appendix: verbatim outside narratives

- [`appendix/carbon_affine_riccati_duality_mpr.md`](appendix/carbon_affine_riccati_duality_mpr.md)
  holds the Gemini "Carbon" disproof of the `←` duality, as pasted by Lars Warren Ericson on
  2026-11-24. It includes the verdict, literature, the 7-step disproof, Lean blueprints and the
  four-pillar roadmap. It was preserved verbatim, previously at
  `SignatureVolatility/SignatureRiccatiKit/AffineRiccatiDualityMpr.md`.
- [`appendix/carbon_nflvr.md`](appendix/carbon_nflvr.md)
  holds a compact excerpt of the Gemini "Carbon" audit of literal and terminal-only NFLVR,
  including the geometric-grid doubling plan and the Black–Scholes transfer $H=K/(S\sigma_0)$,
  as pasted by Lars Warren Ericson. The Lean theorems actually proved are the two compared
  refutations; Carbon's uniformly bounded-below "Result 1" is not formalized here.

**Gaps.** No verbatim Carbon narrative for Theorem C / Proposition 58, the Theorem D residual
hypothesis, or Lemmas 77/78 was found in the repository or in the outside Carbon notes.
narratives for those claims are written from the Lean proofs themselves. If Lars's pasted
narratives for them are recovered, they belong in `appendix/`.
