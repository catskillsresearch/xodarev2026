module

public import SignatureVolatility.HypH1
public import SignatureVolatility.HypH2
public import SignatureVolatility.HypH3
public import SignatureVolatility.ItoCalculusKit.MathFinBridge
public import SignatureVolatility.ItoCalculusKit.SigmaContinuity
public import SignatureVolatility.DualPairing
public import SignatureVolatility.ProlongedBrownianSetup.SignatureFiltration
public import SignatureVolatility.ProlongedBrownianSetup.StratonovichOfBM
public import SignatureVolatility.ProlongedBrownianSetup.WHat
public import SignatureVolatility.Weight


@[expose] public section

open MeasureTheory Set

noncomputable section

namespace SignatureVolatility

/-!
# Novikov–Doob L² martingale package under HypH3

Under H1–H3 and the strengthened continuous independent driver, the Doléans price
is a square-integrable martingale on the signature filtration, with an a.e. L² envelope
and pathwise `IntegrableOn σ²`. Analytic content: Novikov from H3 (`λ = 1/2`), Doob
maximal inequality, and Gaussian signature moments of `σ` under `pathContinuous`.

The driver's coordinate **processes** are independent (`MultiBrownian.coordsIndep`), so `W` is a
Brownian motion in its joint filtration and `σ = ⟨ℓ, Ŵ⟩` is non-anticipating for the driver
coordinate; with independence only at each fixed time, future-entangled coordinates would refute
the martingale property.
-/

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {d : ℕ}

/-- **Remaining analytic gap.** Novikov–Doob for a positive-dimensional driver: the Doléans price
is a martingale on the signature filtration with a square-integrable envelope on `[0, T]`.
The pathwise `IntegrableOn σ²` part and the `d = 0` case are proved in
`kit_novikov_doob_l2_martingale`. -/
theorem kit_novikov_doob_l2_martingale_of_driver {T : ℝ} (B : MultiBrownian Ω P d) (_hd : 0 < d)
    (hT : 0 < T) (w : Weight) (_hw : HypH2 w) (ℓ : ExtTensorAlgebra (d + 1))
    (_hℓ : HypH1 w ℓ) (s₀ : ℝ) (_hs₀ : 0 < s₀) :
    let setup := prolongedBrownianSetup_stratonovich_of_brownian B hT
    let σ : ℝ → Ω → ℝ := fun t ω => dualPairing ℓ (setup.W_hat t ω)
    let S : ℝ → Ω → ℝ := fun t ω => s₀ * kitDoleansExp B σ t ω
    HypH3 P T σ →
    (∀ ⦃s t : ℝ⦄, 0 ≤ s → s ≤ t → t ≤ T →
      Integrable (S t) P ∧
      P[S t | setup.signatureFiltration.σAlg s] =ᵐ[P] S s) ∧
    (∃ S_sup : Ω → ℝ, Measurable S_sup ∧
      (∀ᵐ ω ∂P, ∀ t ∈ Icc 0 T, |S t ω| ≤ S_sup ω) ∧
      Integrable (fun ω => (S_sup ω) ^ 2) P) := by
  sorry

/-- No Brownian driver: the kit Doléans exponential is identically `1`. -/
lemma kitDoleansExp_of_no_driver (B : MultiBrownian Ω P d) (hd : ¬ 0 < d) (σ : ℝ → Ω → ℝ)
    (t : ℝ) (ω : Ω) : kitDoleansExp B σ t ω = 1 := by
  have hIto0 : kitItoIntRaw B σ t = fun _ => 0 := by funext; simp [kitItoIntRaw, hd]
  have hQV0 : kitQuadVarRaw B σ t = fun _ => 0 := by funext; simp [kitQuadVarRaw, hd]
  have hPair : kitPairIntegrable B σ t := ⟨by simp [hIto0], by simp [hQV0]⟩
  simp [kitDoleansExp, kitItoInt, kitQuadVar, hPair, hIto0, hQV0,
    condExp_const ((pathFiltration B).le_ambient t) (0 : ℝ), Real.exp_zero]

/-- Novikov–Doob L² martingale package under H1–H3. -/
theorem kit_novikov_doob_l2_martingale {T : ℝ} (B : MultiBrownian Ω P d) (hT : 0 < T)
    (w : Weight) (_hw : HypH2 w) (ℓ : ExtTensorAlgebra (d + 1))
    (_hℓ : HypH1 w ℓ) (s₀ : ℝ) (_hs₀ : 0 < s₀) :
    let setup := prolongedBrownianSetup_stratonovich_of_brownian B hT
    let σ : ℝ → Ω → ℝ := fun t ω => dualPairing ℓ (setup.W_hat t ω)
    let S : ℝ → Ω → ℝ := fun t ω => s₀ * kitDoleansExp B σ t ω
    HypH3 P T σ →
    (∀ ⦃s t : ℝ⦄, 0 ≤ s → s ≤ t → t ≤ T →
      Integrable (S t) P ∧
      P[S t | setup.signatureFiltration.σAlg s] =ᵐ[P] S s) ∧
    (∃ S_sup : Ω → ℝ, Measurable S_sup ∧
      (∀ᵐ ω ∂P, ∀ t ∈ Icc 0 T, |S t ω| ≤ S_sup ω) ∧
      Integrable (fun ω => (S_sup ω) ^ 2) P) ∧
    (∀ᵐ ω ∂P, IntegrableOn (fun s => (σ s ω) ^ 2) (Icc 0 T) volume) := by
  intro setup σ S h3
  have hint : ∀ᵐ ω ∂P, IntegrableOn (fun s => (σ s ω) ^ 2) (Icc 0 T) volume :=
    ae_of_all P fun ω =>
      ((continuousOn_sigma_of_brownian B hT w _hw ℓ _hℓ ω).pow 2).integrableOn_compact
        isCompact_Icc
  by_cases hd : 0 < d
  · obtain ⟨h1, h2⟩ := kit_novikov_doob_l2_martingale_of_driver B hd hT w _hw ℓ _hℓ s₀ _hs₀ h3
    exact ⟨h1, h2, hint⟩
  · have hS : ∀ t, S t = fun _ => s₀ := fun t => funext fun ω => by
      show s₀ * kitDoleansExp B σ t ω = s₀
      rw [kitDoleansExp_of_no_driver B hd, mul_one]
    refine ⟨fun s t _ _ _ => ⟨?_, ?_⟩, ⟨fun _ => |s₀|, measurable_const,
      ae_of_all _ fun ω t _ => by rw [hS], integrable_const _⟩, hint⟩
    · rw [hS t]; exact integrable_const _
    · rw [hS t, hS s, condExp_const (setup.signatureFiltration.le_ambient s) s₀]

end SignatureVolatility
