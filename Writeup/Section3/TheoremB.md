# Theorem B — EMM / NFLVR and Riccati duality

@import "TheoremB_ailean.txt" {code_block=false}

Paper: Xodarev Theorem B. Under H1–H3 and a `SignatureRiccatiKit`:

1. $S$ is a true $(\mathcal F^{\widehat W}_t,\mathbb P)$-martingale on $[0,T]$; 2. NFLVR holds for admissible gains; 3. every finite signature coordinate is a special semimartingale; 4. nonempty classical Riccati solutions are equivalent (via the kit) to the exponential-affine conditional transform representation.

Builds on `theorem_A`, `nflvr_of_martingale_measure`, and `SignatureRiccatiKit.affine_riccati_duality`. Clause (3) is stated with `Nonempty (IsSpecialSemimartingale …)` because the Lean object is a structure, not a `Prop`. Entry point: `theorem_B`.

**[SignatureVolatility/TheoremB.lean](../../SignatureVolatility/TheoremB.lean)**

@import "../../SignatureVolatility/TheoremB.lean"
