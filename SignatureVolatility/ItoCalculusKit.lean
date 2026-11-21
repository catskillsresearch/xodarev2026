module

public import SignatureVolatility.DualPairing
public import SignatureVolatility.ExtTensorAlgebra.ExtTensorAlgebra
public import SignatureVolatility.HypH1
public import SignatureVolatility.HypH2
public import SignatureVolatility.HypH3
public import SignatureVolatility.Norm2w
public import SignatureVolatility.ProlongedBrownianSetup
public import SignatureVolatility.ProlongedBrownianSetup.SignatureFiltration
public import SignatureVolatility.ProlongedBrownianSetup.WHat
public import SignatureVolatility.Weight


@[expose] public section

noncomputable section

open MeasureTheory Set

namespace SignatureVolatility

/-- Itô calculus kit. Uniqueness is stated up to **modification** (not indistinguishability),
matching SDE hypotheses that constrain each fixed time only almost surely. Novikov/Doob
requires the paper's exponential-integrability hypothesis `HypH3` on the integrand `σ`. -/
structure ItoCalculusKit (Ω : Type*) [m₀ : MeasurableSpace Ω]
    (ℙ : Measure Ω) [IsProbabilityMeasure ℙ] (d : ℕ) (T : ℝ)
    (setup : ProlongedBrownianSetup Ω ℙ d T) where
  itoInt : (ℝ → Ω → ℝ) → ℝ → Ω → ℝ
  itoInt_zero : ∀ H ω, itoInt H 0 ω = 0
  itoInt_meas : ∀ H t, Measurable (itoInt H t)
  itoInt_adapted : ∀ (H : ℝ → Ω → ℝ) (t : ℝ) (s : {s : ℝ // 0 ≤ s ∧ s ≤ t}),
    Measurable[setup.signatureFiltration.σAlg t] (itoInt H s.1)
  quadVar : (ℝ → Ω → ℝ) → ℝ → Ω → ℝ
  quadVar_zero : ∀ H ω, quadVar H 0 ω = 0
  quadVar_meas : ∀ H t, Measurable (quadVar H t)
  quadVar_adapted : ∀ (H : ℝ → Ω → ℝ) (t : ℝ) (s : {s : ℝ // 0 ≤ s ∧ s ≤ t}),
    Measurable[setup.signatureFiltration.σAlg t] (quadVar H s.1)
  doleansExp : (ℝ → Ω → ℝ) → ℝ → Ω → ℝ
  doleansExp_def : ∀ σ t ω,
    doleansExp σ t ω = Real.exp (itoInt σ t ω - (1 / 2 : ℝ) * quadVar σ t ω)
  doleans_sde : ∀ (s₀ : ℝ) (σ : ℝ → Ω → ℝ),
    (∀ᵐ ω ∂ℙ, IntegrableOn (fun s => (σ s ω) ^ 2) (Icc 0 T) volume) →
    ∀ t ∈ Icc 0 T, ∀ᵐ ω ∂ℙ,
      s₀ * doleansExp σ t ω = s₀ + itoInt (fun s ω' => (s₀ * doleansExp σ s ω') * σ s ω') t ω
  /-- L² localisation / Gronwall package. Conclusion is uniqueness **up to modification**. -/
  stopped_l2_localisation : ∀ (w : Weight) (ℓ : ExtTensorAlgebra (d + 1)) (s₀ : ℝ)
    (S₁ S₂ : ℝ → Ω → ℝ),
    let σ : ℝ → Ω → ℝ := fun t ω => dualPairing ℓ (setup.W_hat t ω)
    (∀ t ∈ Icc 0 T, ∀ᵐ ω ∂ℙ, S₁ t ω = s₀ + itoInt (fun s ω' => S₁ s ω' * σ s ω') t ω) →
    (∀ t ∈ Icc 0 T, ∀ᵐ ω ∂ℙ, S₂ t ω = s₀ + itoInt (fun s ω' => S₂ s ω' * σ s ω') t ω) →
    (∃ f : ℕ → ℝ → ℝ,
      (∀ k, ContinuousOn (f k) (Icc 0 T)) ∧
      (∀ k, ∀ t ∈ Icc 0 T, 0 ≤ f k t) ∧
      (∀ k, ∀ t ∈ Icc 0 T,
        f k t ≤ ((k : ℝ) * norm2w w ℓ) ^ 2 * ∫ s in (0 : ℝ)..t, f k s) ∧
      ((∀ k, ∀ t ∈ Icc 0 T, f k t = 0) →
        ∀ t ∈ Icc 0 T, ∀ᵐ ω ∂ℙ, S₁ t ω = S₂ t ω))
  /-- Novikov–Doob L² martingale package under H1–H2 and the analytic H3 on `σ`. -/
  novikov_doob_l2_martingale : ∀ (w : Weight) (_hw : HypH2 w) (ℓ : ExtTensorAlgebra (d + 1))
    (_hℓ : HypH1 w ℓ) (s₀ : ℝ) (_hs₀ : 0 < s₀),
    let σ : ℝ → Ω → ℝ := fun t ω => dualPairing ℓ (setup.W_hat t ω)
    let S : ℝ → Ω → ℝ := fun t ω => s₀ * doleansExp σ t ω
    HypH3 ℙ T σ →
    (∀ ⦃s t : ℝ⦄, 0 ≤ s → s ≤ t → t ≤ T →
      Integrable (S t) ℙ ∧
      ℙ[S t | setup.signatureFiltration.σAlg s] =ᵐ[ℙ] S s) ∧
    (∃ S_sup : Ω → ℝ, Measurable S_sup ∧
      (∀ ω, ∀ t ∈ Icc 0 T, |S t ω| ≤ S_sup ω) ∧
      Integrable (fun ω => (S_sup ω) ^ 2) ℙ) ∧
    (∀ᵐ ω ∂ℙ, IntegrableOn (fun s => (σ s ω) ^ 2) (Icc 0 T) volume)

end SignatureVolatility
