# §3 Theorem B — NFLVR and Riccati duality

Paper: Theorem B / §4 (true martingale & NFLVR under H3; special semimartingales of signature coordinates; affine–Riccati duality for finite transforms).

Subsections follow Lean import order; labels are mathematical English.

- [Theorem B (statement and proof)](Section3/TheoremB.md)
- [Supporting modules](Section3/SupportingModules.md)

The paper's `←` affine / Riccati duality is false as a universal statement. The false theorem `affine_riccati_duality_mpr` has been removed from the library; the counterexample and `not_affine_riccati_duality_mpr` live in `SignatureVolatility/SignatureRiccatiKit/AffineRiccatiDualityMprCounterexample.lean`. Notes: [`SupportingModules/AffineRiccatiDualityMpr.md`](Section3/SupportingModules/AffineRiccatiDualityMpr.md) and [`Writeup/narratives/appendix/carbon_affine_riccati_duality_mpr.md`](narratives/appendix/carbon_affine_riccati_duality_mpr.md). The refutation is proved sorry-free, and `not_affine_riccati_duality_mpr`, `not_affine_riccati_duality`, `not_theorem_B_mpr` and `not_theorem_B` are compared in `comparator.json`. Why the counterexample works: [`narratives/affine_riccati_duality_mpr.md`](narratives/affine_riccati_duality_mpr.md).

The paper's literal NFLVR (Defs 2.17 and 4.3, no wealth lower bound) and the terminal-only bound in Section 4.6 are both false for Black–Scholes. The compared refutations are `not_literal_nflvr_unwrapped` and `not_terminal_bdd_nflvr_unwrapped`, from a geometric-grid doubling strategy due to Gemini "Carbon" and transferred by $H=K/(S\sigma_0)$. Why: [`narratives/nflvr_literal.md`](narratives/nflvr_literal.md). The NFLVR conjunct of `theorem_B_mp` still uses `AdmissibleGainsUnderP`, not the Delbaen–Schachermayer uniformly bounded-below cone; that upgrade is not claimed here.
