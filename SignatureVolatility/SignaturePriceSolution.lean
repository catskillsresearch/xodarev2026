module

public import SignatureVolatility.ItoCalculusKit
public import SignatureVolatility.ProlongedBrownianSetup
public import SignatureVolatility.ProlongedBrownianSetup.SignatureFiltration
public import SignatureVolatility.ProlongedBrownianSetup.WHat
public import SignatureVolatility.SignatureVolatilityModel
public import SignatureVolatility.SignatureVolatilityModel.Sigma


@[expose] public section

noncomputable section

open MeasureTheory Set

namespace SignatureVolatility

structure SignaturePriceSolution {Ω : Type*} [MeasurableSpace Ω]
    {ℙ : Measure Ω} [IsProbabilityMeasure ℙ]
    (M : SignatureVolatilityModel) (setup : ProlongedBrownianSetup Ω ℙ M.d M.T)
    (ito : ItoCalculusKit Ω ℙ M.d M.T setup) where
  S : ℝ → Ω → ℝ
  S_zero : ∀ ω, S 0 ω = M.s₀
  S_meas : ∀ t, Measurable (S t)
  S_adapted : ∀ t (s : {s : ℝ // 0 ≤ s ∧ s ≤ t}),
    Measurable[setup.signatureFiltration.σAlg t] (S s.1)
  S_strictly_pos : ∀ t ω, 0 < S t ω
  doleans_repr : ∀ t ω,
    S t ω = M.s₀ * Real.exp (ito.itoInt (SignatureVolatilityModel.sigma M setup) t ω -
      (1 / 2 : ℝ) * ito.quadVar (SignatureVolatilityModel.sigma M setup) t ω)
  solves_sde : ∀ t ∈ Icc 0 M.T, ∀ᵐ ω ∂ℙ,
    S t ω = M.s₀ + ito.itoInt (fun s ω' => S s ω' * SignatureVolatilityModel.sigma M setup s ω') t ω
  sup_l2_integrable : ∃ S_sup : Ω → ℝ, Measurable S_sup ∧
    (∀ ω, ∀ t ∈ Icc 0 M.T, |S t ω| ≤ S_sup ω) ∧
    Integrable (fun ω => (S_sup ω) ^ 2) ℙ
  is_martingale : ∀ ⦃s t : ℝ⦄, 0 ≤ s → s ≤ t → t ≤ M.T →
    Integrable (S t) ℙ ∧
    ℙ[S t | setup.signatureFiltration.σAlg s] =ᵐ[ℙ] S s

end SignatureVolatility
