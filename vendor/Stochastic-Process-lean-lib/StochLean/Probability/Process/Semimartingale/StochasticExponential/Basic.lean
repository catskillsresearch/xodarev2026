/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Analysis.PathVariation.ExponentialJumpFactor
public import StochLean.Probability.Process.Semimartingale.QuadraticVariation.ContinuousPart

/-! # The actual product expression for the stochastic exponential

The expression uses the existing canonical continuous bracket. Its initial
value is exp(X(0)); the source unit-initial equation will require X(0) = 0.
Product convergence is proved here. Semimartingale regularity and the
defining stochastic equation are separate obligations, not assumed fields.
-/

@[expose] public section

open MeasureTheory Set StochLean
open scoped NNReal

namespace ProbabilityTheory

noncomputable def stochasticExponentialJumpProduct {Ω : Type*}
    (X : ℝ≥0 → Ω → ℝ) (t : ℝ≥0) (ω : Ω) : ℝ :=
  ∏' s : Ioc 0 t, exponentialJumpFactor (jumpProcess X s ω)

@[simp] theorem stochasticExponentialJumpProduct_zero {Ω : Type*} (X : ℝ≥0 → Ω → ℝ)
    (ω : Ω) : stochasticExponentialJumpProduct X 0 ω = 1 := by
  simp [stochasticExponentialJumpProduct]

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsFiniteMeasure P]
  {F : Filtration ℝ≥0 mΩ} {X : ℝ≥0 → Ω → ℝ}

theorem IsSemimartingale.multipliable_stochasticExponentialJumpProduct
    (hX : IsSemimartingale X F P) (hF : F.IsUsual P) :
    ∀ᵐ ω ∂P, ∀ t : ℝ≥0,
      Multipliable (fun s : Ioc 0 t ↦ exponentialJumpFactor (jumpProcess X s ω)) := by
  filter_upwards [hX.summable_sq_jumps hF] with ω hω t
  exact multipliable_exponentialJumpFactor (hω t)

omit [IsFiniteMeasure P] in
theorem HasContinuousPaths.stochasticExponentialJumpProduct_eq_one
    (hc : HasContinuousPaths X P) : Indistinguishable (stochasticExponentialJumpProduct X) 1 P := by
  filter_upwards [hc] with ω hω t
  have hj (s : Ioc 0 t) : jumpProcess X s ω = 0 := hω.jumpProcess_eq_zero (ne_of_gt s.2.1)
  simp only [stochasticExponentialJumpProduct, hj, exponentialJumpFactor_zero, tprod_one,
    Pi.one_apply]

noncomputable def IsSemimartingale.stochasticExponential
    (hX : IsSemimartingale X F P) (hF : F.IsUsual P) : ℝ≥0 → Ω → ℝ := fun t ω ↦
  Real.exp (X t ω - (1 / 2 : ℝ) * hX.continuousQuadraticVariation hF t ω) *
    stochasticExponentialJumpProduct X t ω

@[simp] theorem IsSemimartingale.stochasticExponential_zero
    (hX : IsSemimartingale X F P) (hF : F.IsUsual P) (ω : Ω) :
    hX.stochasticExponential hF 0 ω = Real.exp (X 0 ω) := by
  simp only [stochasticExponential, continuousQuadraticVariation_zero, mul_zero, sub_zero,
    stochasticExponentialJumpProduct_zero, mul_one]

theorem IsSemimartingale.stochasticExponential_zero_ae
    (hX : IsSemimartingale X F P) (hF : F.IsUsual P) (h0 : X 0 =ᵐ[P] 0) :
    hX.stochasticExponential hF 0 =ᵐ[P] 1 := by
  filter_upwards [h0] with ω hω
  simp only [stochasticExponential_zero, hω, Pi.zero_apply, Real.exp_zero, Pi.one_apply]

theorem IsSemimartingale.stochasticExponential_of_continuous
    (hX : IsSemimartingale X F P) (hF : F.IsUsual P) (hc : HasContinuousPaths X P) :
    Indistinguishable (hX.stochasticExponential hF)
      (fun t ω ↦ Real.exp (X t ω - (1 / 2 : ℝ) * hX.continuousQuadraticVariation hF t ω)) P := by
  filter_upwards [hc.stochasticExponentialJumpProduct_eq_one] with ω hω t
  simp only [stochasticExponential, hω t, Pi.one_apply, mul_one]

theorem IsSemimartingale.stochasticExponential_eq_zero_of_jump_eq_neg_one
    (hX : IsSemimartingale X F P) (hF : F.IsUsual P) {t s : ℝ≥0} {ω : Ω}
    (hs : s ∈ Ioc 0 t) (hj : jumpProcess X s ω = -1) :
    hX.stochasticExponential hF t ω = 0 := by
  have hprod : stochasticExponentialJumpProduct X t ω = 0 :=
    tprod_of_exists_eq_zero ⟨⟨s, hs⟩, by simp only [hj, exponentialJumpFactor_neg_one]⟩
  simp only [stochasticExponential, hprod, mul_zero]

end ProbabilityTheory
