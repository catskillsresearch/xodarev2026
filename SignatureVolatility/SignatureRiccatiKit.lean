module

public import SignatureVolatility.ClassicalRiccatiSolution
public import SignatureVolatility.DualPairing
public import SignatureVolatility.ExtTensorAlgebra.FreeTensorAlgebra
public import SignatureVolatility.IsSpecialSemimartingale
public import SignatureVolatility.ProlongedBrownianSetup
public import SignatureVolatility.ProlongedBrownianSetup.SignatureFiltration
public import SignatureVolatility.ProlongedBrownianSetup.WHat
public import SignatureVolatility.SignatureVolatilityModel
public import SignatureVolatility.Weight
public import SignatureVolatility.Word


@[expose] public section

noncomputable section

open MeasureTheory Set

namespace SignatureVolatility

/-- **Transform finiteness** (paper Theorem 44(2) hypothesis), for one initial datum `u₀`: the
signature transform `𝔼 exp⟨u₀, Ŵ_t⟩` is finite on `[0, T]`. The paper quantifies this over *all*
`u₀ ∈ 𝒟_fin`; that global version fails for Brownian signatures (`u₀ = c e_{11}` gives
`𝔼 exp(c W_t² / 2) = ∞` once `c t ≥ 1`), so it is imposed per initial datum. -/
def SignatureTransformFinite {Ω : Type*} [MeasurableSpace Ω] (ℙ : Measure Ω) {d : ℕ} {T : ℝ}
    [IsProbabilityMeasure ℙ] (setup : ProlongedBrownianSetup Ω ℙ d T) (u₀ : ExtTensorAlgebra (d + 1)) :
    Prop :=
  ∀ t ∈ Icc 0 T, Integrable (fun ω => Real.exp (dualPairing u₀ (setup.W_hat t ω))) ℙ

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
    SignatureTransformFinite ℙ setup u₀.1 →
    ((∃ sol : ClassicalRiccatiSolution M.w M.T R_op u₀.1,
      ∀ t ∈ Icc 0 M.T,
        Integrable (fun ω => Real.exp (dualPairing u₀.1 (setup.W_hat M.T ω))) ℙ ∧
        ℙ[fun ω => Real.exp (dualPairing u₀.1 (setup.W_hat M.T ω)) |
          setup.signatureFiltration.σAlg t] =ᵐ[ℙ]
          fun ω => Real.exp (dualPairing (sol.ψ (M.T - t)) (setup.W_hat t ω))) ↔
    Nonempty (ClassicalRiccatiSolution M.w M.T R_op u₀.1))

end SignatureVolatility
