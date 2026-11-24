# §3 Theorem B — NFLVR and Riccati duality

Paper: Theorem B / §4 (true martingale & NFLVR under H3; special semimartingales of signature coordinates; affine–Riccati duality for finite transforms).

Subsections follow Lean import order; labels are mathematical English.

- [Theorem B (statement and proof)](Section3/TheoremB.md)
- [Supporting modules](Section3/SupportingModules.md)

The paper's `←` affine / Riccati duality is false as a universal statement. The false theorem `affine_riccati_duality_mpr` has been removed from the library; the counterexample and `not_affine_riccati_duality_mpr` live in `SignatureVolatility/SignatureRiccatiKit/AffineRiccatiDualityMprCounterexample.lean`. Notes: [`SupportingModules/AffineRiccatiDualityMpr.md`](Section3/SupportingModules/AffineRiccatiDualityMpr.md) and [`SignatureVolatility/SignatureRiccatiKit/AffineRiccatiDualityMpr.md`](../SignatureVolatility/SignatureRiccatiKit/AffineRiccatiDualityMpr.md). The refutation is assembled but still blocked on remaining analytic leaves.
