# Affine / Riccati duality, `←` direction

Paper: Xodarev Theorem 4.2(ii), the backward direction. Lean: `affine_riccati_duality_mpr` in [`SignatureVolatility/SignatureRiccatiKit/AffineRiccatiDualityMpr.lean`](../../../SignatureVolatility/SignatureRiccatiKit/AffineRiccatiDualityMpr.lean).

This is the single remaining `sorry` in the build. The forward direction `affine_riccati_duality_mp` is proved. The paper iff and `signatureRiccatiKit_of_setup` in [`AffineRiccatiDuality.lean`](../../../SignatureVolatility/SignatureRiccatiKit/AffineRiccatiDuality.lean), and `theorem_B_mpr` / `theorem_B` in [`TheoremBMpr.lean`](../../../SignatureVolatility/TheoremBMpr.lean), are blocked only on this lemma.

**Proposed counterexample (unverified).** Gemini Carbon (outside opinion, 2026-11-24) claims the lemma is false as stated: for every model and Brownian motion there is a finitely supported family $u_0^{(\lambda)}$ meeting both hypotheses while the conclusion fails. Pillars A–D of that argument are still `sorry`. The citation arXiv:2606.29622 has not been verified by us. The writeup has not been compiled in this repository, and no Lean from it has been added to the build.

Full memorialization (verdict, literature, 7-step disproof, both Lean blueprints, roadmap): [`SignatureVolatility/SignatureRiccatiKit/AffineRiccatiDualityMpr.md`](../../../SignatureVolatility/SignatureRiccatiKit/AffineRiccatiDualityMpr.md).
