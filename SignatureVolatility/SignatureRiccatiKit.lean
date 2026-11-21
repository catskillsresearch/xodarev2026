import SignatureVolatility.ClassicalRiccatiSolution
import SignatureVolatility.DualPairing
import SignatureVolatility.ExtTensorAlgebra.FreeTensorAlgebra
import SignatureVolatility.IsSpecialSemimartingale
import SignatureVolatility.ProlongedBrownianSetup
import SignatureVolatility.ProlongedBrownianSetup.SignatureFiltration
import SignatureVolatility.ProlongedBrownianSetup.WHat
import SignatureVolatility.SignatureVolatilityModel
import SignatureVolatility.Weight
import SignatureVolatility.Word

noncomputable section

open MeasureTheory Set

namespace SignatureVolatility

structure SignatureRiccatiKit (Ω : Type*) [MeasurableSpace Ω]
    (ℙ : Measure Ω) [IsProbabilityMeasure ℙ]
    (M : SignatureVolatilityModel) (setup : ProlongedBrownianSetup Ω ℙ M.d M.T) where
  /-- Every finite coordinate `t ↦ ⟨e_I, Ŵ_t⟩` is a special semimartingale on `[0, T]`. -/
  coord_special_semimartingale : ∀ I : Word (M.d + 1),
    IsSpecialSemimartingale ℙ setup.signatureFiltration M.T (fun t ω => (setup.W_hat t ω).coeff I)
  /-- Riccati vector field `ℛ` on `T_w` extending `riccatiOpBounded` from `𝒟_fin`. -/
  R_op : ExtTensorAlgebra (M.d + 1) → ExtTensorAlgebra (M.d + 1)
  /-- Equivalence between global classical Riccati solvability on `[0, T]` and bounded
  exponential-affine conditional signature transforms `E[exp(⟨u₀, Ŵ_T⟩) | ℱ^{\widehat{W}}_t] =
  exp(⟨ψ(T - t), Ŵ_t⟩)` for `u₀ ∈ 𝒟_fin` (Theorem 4.2(4)). -/
  affine_riccati_duality : ∀ (u₀ : ExtTensorAlgebra.FreeTensorAlgebra (M.d + 1)),
    (∃ sol : ClassicalRiccatiSolution M.w M.T R_op u₀.1,
      ∀ t ∈ Icc 0 M.T,
        Integrable (fun ω => Real.exp (dualPairing u₀.1 (setup.W_hat M.T ω))) ℙ ∧
        ℙ[fun ω => Real.exp (dualPairing u₀.1 (setup.W_hat M.T ω)) |
          setup.signatureFiltration.σAlg t] =ᵐ[ℙ]
          fun ω => Real.exp (dualPairing (sol.ψ (M.T - t)) (setup.W_hat t ω))) ↔
    Nonempty (ClassicalRiccatiSolution M.w M.T R_op u₀.1)

end SignatureVolatility