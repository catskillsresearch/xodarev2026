# Affine Riccati Duality

@import "AffineRiccatiDuality_ailean.txt" {code_block=false}

Paper: Xodarev Theorem 4.2. Paper Theorem 4.2(ii) claimed, for every finitely supported `u₀` with finite signature transform, that the exponential-affine conditional transform identity holds if and only if a global classical Riccati solution exists. The `→` direction is true (`affine_riccati_duality_mp`). The `←` direction is false as a universal statement: `not_affine_riccati_duality_mpr`.

**[SignatureVolatility/SignatureRiccatiKit/AffineRiccatiDuality.lean](../../../../SignatureVolatility/SignatureRiccatiKit/AffineRiccatiDuality.lean)**

@import "../../../../SignatureVolatility/SignatureRiccatiKit/AffineRiccatiDuality.lean"
