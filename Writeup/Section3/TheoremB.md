# Theorem B — EMM / NFLVR and Riccati duality

@import "TheoremB_ailean.txt" {code_block=false}

Paper: Xodarev Theorem B. Under H1–H3 and a `SignatureRiccatiKit`:

1. $S$ is a true $(\mathcal F^{\widehat W}_t,\mathbb P)$-martingale on $[0,T]$; 2. NFLVR holds for admissible gains; 3. every finite signature coordinate is a special semimartingale; 4. nonempty classical Riccati solutions are equivalent (via the kit) to the exponential-affine conditional transform representation.

The proved entry point is `theorem_B_mp` (martingale, NFLVR, special-semimartingale coordinates, and the `→` Riccati direction). Clause (3) is stated with `Nonempty (IsSpecialSemimartingale …)` because the Lean object is a structure, not a `Prop`. The paper's full Theorem B (including the `←` iff) is false; see `not_theorem_B`.

**[SignatureVolatility/TheoremB.lean](../../SignatureVolatility/TheoremB.lean)**

@import "../../SignatureVolatility/TheoremB.lean"

**The `←` direction is false.** The false theorem `affine_riccati_duality_mpr` has been removed. Its negation `not_affine_riccati_duality_mpr` is assembled in the counterexample module; `not_theorem_B_mpr` and `not_theorem_B` hang off it. All are proved sorry-free and compared. Why: [`narratives/affine_riccati_duality_mpr.md`](../narratives/affine_riccati_duality_mpr.md). See also [`SupportingModules/AffineRiccatiDualityMpr.md`](SupportingModules/AffineRiccatiDualityMpr.md) and [`Writeup/narratives/appendix/carbon_affine_riccati_duality_mpr.md`](../narratives/appendix/carbon_affine_riccati_duality_mpr.md).
