# Affine Riccati Duality Mp

@import "AffineRiccatiDualityMp_ailean.txt" {code_block=false}

Paper: Xodarev Theorem 4.2. Paper Theorem 4.2(ii) (p. 21) states, for finitely supported `u₀` with finite signature transform, that the conditional transform is exponential-affine, `𝔼[exp⟨u₀, Ŵ_T⟩ | ℱ_t] = exp⟨ψ(T − t), Ŵ_t⟩` for a classical solution `ψ` of `∂ψ = ℛ(ψ)`, `ψ(0) = u₀`, **iff** a global classical Riccati solution exists. This file proves the `→` direction (`affine_riccati_duality_mp`): an exponential-affine representation through a classical Riccati solution yields such a solution.

@import "../../../../SignatureVolatility/SignatureRiccatiKit/AffineRiccatiDualityMp.lean"
