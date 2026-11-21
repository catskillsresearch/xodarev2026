/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Martingale.OptionalSampling.PredictableJump
public import StochLean.Probability.Process.Stopping.PredictableValue
public import Mathlib.MeasureTheory.Function.ConditionalExpectation.PullOut

/-! # Bounded before-field multipliers of predictable martingale jumps

The actual stopped jump is integrable by the bounded predictable sampling
theorem. A bounded multiplier known strictly before the stopping time gives
an integrable product by norm domination. Native conditional-expectation
pull-out then proves zero conditional mean, hence zero expectation.

The predictable-process consumer uses the existing stopped-value owner.
Only its sampled multiplier is required bounded; no path regularity of that
predictable process is assumed. The bound on the stopping time proves its
finiteness before finite evaluation replaces the explicit terminal owner.
These results concern one bounded predictable stopping time and are not a
general Yoeurp theorem or a claim that the actual jump vanishes.
-/

@[expose] public section

open ProbabilityTheory Filter
open scoped NNReal ENNReal

namespace MeasureTheory.Martingale

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsFiniteMeasure P]
  {F : Filtration ℝ≥0 mΩ} {M : ℝ≥0 → Ω → ℝ} {τ : Ω → WithTop ℝ≥0} {T : ℝ≥0}
  {K : Ω → ℝ}

/-- The product is actually integrable, with norm bounded by `C` times the
norm of the integrable jump. No pull-out conclusion is used for this step. -/
theorem integrable_mul_stopped_jump_of_predictable_of_bounded
    (hM : Martingale M F P) (hF : F.IsUsual P) (hc : HasCadlagPaths M P)
    (hτ : IsPredictableStoppingTime F τ P) (hpos : ∀ᵐ ω ∂P, 0 < τ ω)
    (hb : ∀ ω, τ ω ≤ (T : WithTop ℝ≥0))
    (hK : StronglyMeasurable[hτ.1.measurableSpaceBefore] K)
    (C : ℝ) (hKb : ∀ᵐ ω ∂P, ‖K ω‖ ≤ C) :
    Integrable (K * stoppedValue (jumpProcess M) τ) P := by
  have hi := hM.integrable_stopped_jump_of_predictable_of_bounded hF hc hτ hpos hb
  apply (hi.norm.const_mul C).mono'
    ((hK.mono hτ.1.measurableSpaceBefore_le_ambient).aestronglyMeasurable.mul
      hi.aestronglyMeasurable)
  filter_upwards [hKb] with ω hω
  change ‖K ω * stoppedValue (jumpProcess M) τ ω‖ ≤
    C * ‖stoppedValue (jumpProcess M) τ ω‖
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_right hω (norm_nonneg _)

/-- A bounded multiplier measurable before the stopping time preserves the
zero conditional mean of the actual martingale jump. -/
theorem condExp_mul_stopped_jump_before_ae_eq_zero_of_predictable_of_bounded
    (hM : Martingale M F P) (hF : F.IsUsual P) (hc : HasCadlagPaths M P)
    (hτ : IsPredictableStoppingTime F τ P) (hpos : ∀ᵐ ω ∂P, 0 < τ ω)
    (hb : ∀ ω, τ ω ≤ (T : WithTop ℝ≥0))
    (hK : StronglyMeasurable[hτ.1.measurableSpaceBefore] K)
    (C : ℝ) (hKb : ∀ᵐ ω ∂P, ‖K ω‖ ≤ C) :
    P[K * stoppedValue (jumpProcess M) τ | hτ.1.measurableSpaceBefore] =ᵐ[P] 0 := by
  have hi := hM.integrable_stopped_jump_of_predictable_of_bounded hF hc hτ hpos hb
  have hip := hM.integrable_mul_stopped_jump_of_predictable_of_bounded
    hF hc hτ hpos hb hK C hKb
  have hout := condExp_mul_of_stronglyMeasurable_left hK hip hi
  have hz := hM.condExp_stopped_jump_before_ae_eq_zero_of_predictable_of_bounded
    hF hc hτ hpos hb
  filter_upwards [hout, hz] with ω hp hω
  change P[K * stoppedValue (jumpProcess M) τ | hτ.1.measurableSpaceBefore] ω = 0
  rw [hp]
  change K ω * P[stoppedValue (jumpProcess M) τ | hτ.1.measurableSpaceBefore] ω = 0
  rw [hω, Pi.zero_apply, mul_zero]

/-- The expectation is zero for the actual integrable weighted jump. -/
theorem integral_mul_stopped_jump_eq_zero_of_predictable_of_bounded
    (hM : Martingale M F P) (hF : F.IsUsual P) (hc : HasCadlagPaths M P)
    (hτ : IsPredictableStoppingTime F τ P) (hpos : ∀ᵐ ω ∂P, 0 < τ ω)
    (hb : ∀ ω, τ ω ≤ (T : WithTop ℝ≥0))
    (hK : StronglyMeasurable[hτ.1.measurableSpaceBefore] K)
    (C : ℝ) (hKb : ∀ᵐ ω ∂P, ‖K ω‖ ≤ C) :
    (∫ ω, K ω * stoppedValue (jumpProcess M) τ ω ∂P) = 0 := by
  have hz := hM.condExp_mul_stopped_jump_before_ae_eq_zero_of_predictable_of_bounded
    hF hc hτ hpos hb hK C hKb
  calc
    (∫ ω, K ω * stoppedValue (jumpProcess M) τ ω ∂P) =
        ∫ ω, P[K * stoppedValue (jumpProcess M) τ | hτ.1.measurableSpaceBefore] ω ∂P :=
      (integral_condExp hτ.1.measurableSpaceBefore_le_ambient).symm
    _ = 0 := by
      simpa only [Pi.zero_apply, integral_zero] using integral_congr_ae hz

/-- A predictable process supplies the before-field multiplier through its
actual finite stopping evaluation. Only the sampled values must be bounded. -/
theorem predictable_multiplier_stopped_jump_of_bounded
    (hM : Martingale M F P) (hF : F.IsUsual P) (hc : HasCadlagPaths M P)
    (hτ : IsPredictableStoppingTime F τ P) (hpos : ∀ᵐ ω ∂P, 0 < τ ω)
    (hb : ∀ ω, τ ω ≤ (T : WithTop ℝ≥0))
    {H : ℝ≥0 → Ω → ℝ} (hH : IsStronglyPredictable F H)
    (C : ℝ) (hHb : ∀ᵐ ω ∂P, ‖stoppedValue H τ ω‖ ≤ C) :
    Integrable (stoppedValue H τ * stoppedValue (jumpProcess M) τ) P ∧
      P[stoppedValue H τ * stoppedValue (jumpProcess M) τ |
        hτ.1.measurableSpaceBefore] =ᵐ[P] 0 ∧
      (∫ ω, stoppedValue H τ ω * stoppedValue (jumpProcess M) τ ω ∂P) = 0 := by
  have hfinite (ω : Ω) : τ ω ≠ ⊤ :=
    ne_top_of_le_ne_top WithTop.coe_ne_top (hb ω)
  have hz : StronglyMeasurable[⨆ t, F t] (fun _ : Ω ↦ (0 : ℝ)) :=
    stronglyMeasurable_const
  have hK : StronglyMeasurable[hτ.1.measurableSpaceBefore] (stoppedValue H τ) := by
    have hm := hH.stronglyMeasurable_stoppedValueWithTerminal_before hz hτ.1
    have he : stoppedValueWithTerminal H (fun _ ↦ (0 : ℝ)) τ = stoppedValue H τ :=
      funext fun ω ↦ stoppedValueWithTerminal_of_ne_top (hfinite ω)
    rwa [he] at hm
  exact ⟨hM.integrable_mul_stopped_jump_of_predictable_of_bounded
      hF hc hτ hpos hb hK C hHb,
    hM.condExp_mul_stopped_jump_before_ae_eq_zero_of_predictable_of_bounded
      hF hc hτ hpos hb hK C hHb,
    hM.integral_mul_stopped_jump_eq_zero_of_predictable_of_bounded
      hF hc hτ hpos hb hK C hHb⟩

end MeasureTheory.Martingale
