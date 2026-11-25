# Affine / Riccati duality, `←` direction

Paper: Xodarev Theorem 4.2(ii), the backward direction. The false theorem `affine_riccati_duality_mpr` has been removed from the library. The negation `not_affine_riccati_duality_mpr` is assembled in [`AffineRiccatiDualityMprCounterexample.lean`](../../../SignatureVolatility/SignatureRiccatiKit/AffineRiccatiDualityMprCounterexample.lean). `not_affine_riccati_duality` lives in [`AffineRiccatiDuality.lean`](../../../SignatureVolatility/SignatureRiccatiKit/AffineRiccatiDuality.lean); `not_theorem_B_mpr` and `not_theorem_B` live in [`TheoremBMpr.lean`](../../../SignatureVolatility/TheoremBMpr.lean). The proved directions `affine_riccati_duality_mp` and `theorem_B_mp` are kept. The kit constructor `signatureRiccatiKit_of_setup` has been dropped.

The refutation is proved sorry-free, and all four negations are compared in `comparator.json`. Short narrative: [`narratives/affine_riccati_duality_mpr.md`](../../narratives/affine_riccati_duality_mpr.md).

Verbatim Carbon writeup (appendix): [`Writeup/narratives/appendix/carbon_affine_riccati_duality_mpr.md`](../../narratives/appendix/carbon_affine_riccati_duality_mpr.md).
