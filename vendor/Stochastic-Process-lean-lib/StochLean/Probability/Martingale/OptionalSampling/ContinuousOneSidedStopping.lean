/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Martingale.OptionalSampling.ContinuousOneSidedUsual
public import StochLean.Probability.Martingale.OptionalSampling.ContinuousUsual
public import StochLean.Probability.Conditional.StoppingCommutation

/-! # Stopping continuous-time one-sided martingales

Bounded optional sampling first gives an inequality at the minimum stopping
field. The existing stopping-field commutation theorem identifies this
conditional expectation at the original field: its proof splits on the two
events comparing the stopping times. No inequality is lifted directly from
a smaller conditioning field to a larger one.

For stopping the process at an arbitrary lifetime, each coordinate only
samples a bounded minimum. Neither Class D nor boundedness or finiteness of
the lifetime is assumed. The original process needs only common almost-sure
right-continuous paths under the usual conditions.
-/

@[expose] public section

open ProbabilityTheory Filter
open scoped NNReal

namespace MeasureTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsFiniteMeasure P]
  {F : Filtration ℝ≥0 mΩ} {X : ℝ≥0 → Ω → ℝ}

/-- The conditional expectation of a bounded terminal stopping value is
bounded by the value at the minimum. The conditioning field belongs to the
original first stopping time, which may be unbounded or infinite. -/
theorem Supermartingale.condExp_stoppedValue_min_ae_le_of_bounded
    (hX : Supermartingale X F P) (hF : F.IsUsual P)
    (hr : HasRightContinuousPaths X P) {σ τ : Ω → WithTop ℝ≥0}
    (hσ : IsStoppingTime F σ) (hτ : IsStoppingTime F τ) {T : ℝ≥0}
    (hb : ∀ ω, τ ω ≤ T) :
    P[stoppedValue X τ | hσ.measurableSpace] ≤ᵐ[P]
      stoppedValue X (fun ω ↦ min (σ ω) (τ ω)) := by
  have hi := hX.integrable_stoppedValue_of_bounded hτ hb hr
  have hm := (hX.stronglyAdapted.measurable_stoppedValue_of_usual hF hr hτ).stronglyMeasurable
  have he := condExp_stoppingTime_eq_min_of_stronglyMeasurable hσ hτ hi hm
  exact he.le.trans (hX.condExp_stoppedValue_ae_le_of_bounded hF hr (hσ.min hτ) hτ
    (fun _ ↦ min_le_right _ _) hb)

/-- Stopping preserves the supermartingale property for the original
filtration. The lifetime is allowed to be infinite; only its minimum with
each fixed coordinate time is evaluated as a finite stopping value. -/
theorem Supermartingale.stoppedProcess_of_usual
    (hX : Supermartingale X F P) (hF : F.IsUsual P)
    (hr : HasRightContinuousPaths X P) {τ : Ω → WithTop ℝ≥0}
    (hτ : IsStoppingTime F τ) : Supermartingale (stoppedProcess X τ) F P := by
  refine ⟨hX.stronglyAdapted.stoppedProcess_of_usual hF hr hτ, ?_, ?_⟩
  · intro s t hst
    have h := hX.condExp_stoppedValue_min_ae_le_of_bounded hF hr
      (isStoppingTime_const F s) ((isStoppingTime_const F t).min hτ)
      (fun _ ↦ min_le_left _ _)
    rw [IsStoppingTime.measurableSpace_const] at h
    simpa only [stoppedProcess_eq_stoppedValue, ← min_assoc,
      min_eq_left (WithTop.coe_le_coe.mpr hst)] using h
  · intro t
    simpa only [stoppedProcess_eq_stoppedValue] using
      hX.integrable_stoppedValue_of_bounded ((isStoppingTime_const F t).min hτ)
        (fun _ ↦ min_le_left _ _) hr

/-- The submartingale counterpart of the minimum optional-sampling
inequality, with the original first stopping field retained. -/
theorem Submartingale.stoppedValue_min_ae_le_condExp_of_bounded
    (hX : Submartingale X F P) (hF : F.IsUsual P)
    (hr : HasRightContinuousPaths X P) {σ τ : Ω → WithTop ℝ≥0}
    (hσ : IsStoppingTime F σ) (hτ : IsStoppingTime F τ) {T : ℝ≥0}
    (hb : ∀ ω, τ ω ≤ T) :
    stoppedValue X (fun ω ↦ min (σ ω) (τ ω)) ≤ᵐ[P]
      P[stoppedValue X τ | hσ.measurableSpace] := by
  have hrn : HasRightContinuousPaths (-X) P := hr.mono fun _ hω t ↦ (hω t).neg
  have h := hX.neg.condExp_stoppedValue_min_ae_le_of_bounded hF hrn hσ hτ hb
  filter_upwards [h, condExp_neg (stoppedValue X τ) hσ.measurableSpace] with ω hω he
  simpa only [stoppedValue_neg, Pi.neg_apply, he, neg_le_neg_iff] using hω

/-- Stopping also preserves the submartingale property, with no lifetime
bound and no Class D assumption. -/
theorem Submartingale.stoppedProcess_of_usual
    (hX : Submartingale X F P) (hF : F.IsUsual P)
    (hr : HasRightContinuousPaths X P) {τ : Ω → WithTop ℝ≥0}
    (hτ : IsStoppingTime F τ) : Submartingale (stoppedProcess X τ) F P := by
  have hrn : HasRightContinuousPaths (-X) P := hr.mono fun _ hω t ↦ (hω t).neg
  have he : -(stoppedProcess (-X) τ) = stoppedProcess X τ := by
    funext t ω
    exact neg_neg _
  simpa only [he] using (hX.neg.stoppedProcess_of_usual hF hrn hτ).neg

end MeasureTheory
