module

public import SignatureVolatility.ItoCalculusKit
public import SignatureVolatility.ItoCalculusKit.MathFinBridge
public import SignatureVolatility.HypH1
public import SignatureVolatility.HypH2
public import SignatureVolatility.HypH3
public import SignatureVolatility.DualPairing
public import SignatureVolatility.Norm2w
public import SignatureVolatility.ProlongedBrownianSetup.StratonovichOfBM
public import SignatureVolatility.ProlongedBrownianSetup.WHat
public import SignatureVolatility.Weight


@[expose] public section

open MeasureTheory Set

noncomputable section

namespace SignatureVolatility

/-!
# Stopped L² localisation for the paper Itô kit

Gronwall majorants + modification uniqueness for the linear signature SDE
`dS = S · ⟨ℓ, Ŵ⟩ dW`. Analytic content: energy estimates controlled by `norm2w`
under the strengthened continuous independent driver.
-/

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {d : ℕ}

/-- Stopped L² localisation package under H1–H3, for **strong solutions**: adapted to the
signature filtration and in `KitStrongSolutionClass` (square-integrable supremum on `[0, T]` and
`L⁴`-regular integrand `S σ`).

Why these hypotheses (the paper's uniqueness is for strong solutions, i.e. continuous
semimartingales):
* without adaptedness the clause is false: `kitItoInt` zeroes non-measurable integrands
  (`forceMeasurable`), so on an incomplete space `s₀ + 𝟙_A` (`A` a non-measurable subset of a null
  set) is a spurious second solution;
* without H1–H2 the volatility need not have moments (e.g. `σ = exp(W⁴)`, `𝔼 ∫ σ² = ∞`), then
  `kitItoInt (s₀ σ) = 0` and the constant `s₀` solves the kit equation although it is not the
  paper's price;
* without the regularity class an adapted process is not a semimartingale solution: the kit's
  integral at `t` only samples the integrand at `q t`, `q ∈ ℚ`, and is linear / isometric only on
  regular integrands. The constructed Doléans price is in the class
  (`kit_doleans_strong_class`). -/
theorem kit_stopped_l2_localisation {T : ℝ} (B : MultiBrownian Ω P d) (hT : 0 < T)
    (w : Weight) (_hw : HypH2 w) (ℓ : ExtTensorAlgebra (d + 1)) (_hℓ : HypH1 w ℓ) (s₀ : ℝ)
    (S₁ S₂ : ℝ → Ω → ℝ) :
    let setup := prolongedBrownianSetup_stratonovich_of_brownian B hT
    let σ : ℝ → Ω → ℝ := fun t ω => dualPairing ℓ (setup.W_hat t ω)
    HypH3 P T σ →
    (∀ t ∈ Icc 0 T, Measurable[setup.signatureFiltration.σAlg t] (S₁ t)) →
    (∀ t ∈ Icc 0 T, Measurable[setup.signatureFiltration.σAlg t] (S₂ t)) →
    KitStrongSolutionClass P T σ S₁ →
    KitStrongSolutionClass P T σ S₂ →
    (∀ t ∈ Icc 0 T, ∀ᵐ ω ∂P,
      S₁ t ω = s₀ + kitItoInt B (fun s ω' => S₁ s ω' * σ s ω') t ω) →
    (∀ t ∈ Icc 0 T, ∀ᵐ ω ∂P,
      S₂ t ω = s₀ + kitItoInt B (fun s ω' => S₂ s ω' * σ s ω') t ω) →
    ∃ f : ℕ → ℝ → ℝ,
      (∀ k, ContinuousOn (f k) (Icc 0 T)) ∧
      (∀ k, ∀ t ∈ Icc 0 T, 0 ≤ f k t) ∧
      (∀ k, ∀ t ∈ Icc 0 T,
        f k t ≤ ((k : ℝ) * norm2w w ℓ) ^ 2 * ∫ s in (0 : ℝ)..t, f k s) ∧
      ((∀ k, ∀ t ∈ Icc 0 T, f k t = 0) →
        ∀ t ∈ Icc 0 T, ∀ᵐ ω ∂P, S₁ t ω = S₂ t ω) := by
  sorry

end SignatureVolatility
