/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.ClassD.Local
public import StochLean.Probability.Martingale.OptionalSampling.ContinuousOneSidedUsual

/-! # Class DL for nonnegative submartingales

The terminal conditional expectation dominates every nonnegative bounded
stopping value. Its UI gives Class DL. The positivity guard cannot be
dropped merely because bounded stopped values are integrable.
-/

@[expose] public section

open ProbabilityTheory Filter
open scoped NNReal

namespace MeasureTheory.Submartingale

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsFiniteMeasure P]
  {F : Filtration ℝ≥0 mΩ} {X : ℝ≥0 → Ω → ℝ}

theorem isClassDL_of_nonneg (hX : Submartingale X F P)
    (hF : F.IsUsual P) (hr : HasRightContinuousPaths X P)
    (hn : ∀ᵐ ω ∂P, ∀ t, 0 ≤ X t ω) : IsClassDL X F P := by
  intro T
  have hu := (hX.integrable T).uniformIntegrable_condExp
    (fun τ : {τ : FiniteStoppingTime F | ∀ ω, τ ω ≤ T} ↦ τ.1.measurableSpace_le)
  apply hu.mono_norm
  · intro τ
    exact (hX.integrable_finiteStoppingTime_value τ.1 τ.2 hr).aestronglyMeasurable
  · intro τ
    have hle := hX.finiteStoppingTime_value_ae_le_condExp_of_le hF hr τ.1
      (FiniteStoppingTime.const F T) τ.2 (fun _ ↦ le_rfl)
    filter_upwards [hn, hle] with ω hω hl
    change X (τ.1 ω) ω ≤ P[X T | τ.1.measurableSpace] ω at hl
    simpa only [Real.norm_eq_abs, abs_of_nonneg (hω (τ.1 ω)),
      abs_of_nonneg ((hω (τ.1 ω)).trans hl)] using hl

theorem isClassDL_of_ae_nonneg (hX : Submartingale X F P)
    (hF : F.IsUsual P) (hr : HasRightContinuousPaths X P)
    (hn : ∀ t, ∀ᵐ ω ∂P, 0 ≤ X t ω) : IsClassDL X F P := by
  let Y : ℝ≥0 → Ω → ℝ := fun t ω ↦ max (X t ω) 0
  have hY : Submartingale Y F P := hX.sup (martingale_const F P (0 : ℝ)).submartingale
  have hyr : HasRightContinuousPaths Y P :=
    hr.mono fun _ hω t ↦ (hω t).max continuousWithinAt_const
  have hm : IsModification Y X P := fun t ↦ (hn t).mono fun _ hω ↦ max_eq_left hω
  exact (hY.isClassDL_of_nonneg hF hyr (ae_of_all P fun _ _ ↦ le_max_right _ _)).congr
    (hm.indistinguishable_of_rightContinuous hyr hr)

end MeasureTheory.Submartingale
