module

public import SignatureVolatility.HypH1
public import SignatureVolatility.HypH2
public import SignatureVolatility.HypH3
public import SignatureVolatility.ItoCalculusKit.MathFinBridge
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

Under H1–H3 the Doléans price `S = s₀ · ℰ(⟨ℓ, Ŵ⟩)` is a square-integrable martingale on the
signature filtration, with an L² envelope and pathwise `IntegrableOn σ²`. Analytic content:
Novikov from H3 (`λ = 1/2`), bounded approximation via MathFin
`simpleDoleansExp_isMartingale`, UI passage to the limit, Doob maximal inequality, and
`factorial_moment_control` for Gaussian signature moments of `σ`.
-/

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {d : ℕ}

/-- Novikov–Doob L² martingale package under H1–H3. -/
axiom kit_novikov_doob_l2_martingale {T : ℝ} (B : MultiBrownian Ω P d) (hT : 0 < T)
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
      (∀ ω, ∀ t ∈ Icc 0 T, |S t ω| ≤ S_sup ω) ∧
      Integrable (fun ω => (S_sup ω) ^ 2) P) ∧
    (∀ᵐ ω ∂P, IntegrableOn (fun s => (σ s ω) ^ 2) (Icc 0 T) volume)

end SignatureVolatility
