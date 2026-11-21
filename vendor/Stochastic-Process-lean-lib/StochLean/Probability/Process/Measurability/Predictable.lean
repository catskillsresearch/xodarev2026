/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.Measurability.PredictableGrid
public import StochLean.Probability.Process.Measurability.LeftLimit

/-! # Predictability from left-continuous adapted paths

Mathlib's predictable sigma-field remains the canonical owner. Strict-past grids
prove the source Chapter III bridge. For merely almost-sure path regularity a
single exceptional event is removed: the conclusion is an indistinguishable
predictable version, not predictability of arbitrary exceptional trajectories.
This file does not extend the Chapter II integral to all predictable integrands.
-/

@[expose] public section

open ProbabilityTheory Filter Set
open scoped NNReal Topology

namespace MeasureTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {F : Filtration ℝ≥0 mΩ}
  {X : ℝ≥0 → Ω → ℝ} {P : Measure Ω}

theorem Adapted.isStronglyPredictable_of_leftContinuous (ha : Adapted F X)
    (hc : ∀ ω, IsLeftContinuousPath (fun t ↦ X t ω)) : IsStronglyPredictable F X := by
  let : MeasurableSpace (ℝ≥0 × Ω) := F.predictable
  change StronglyMeasurable (Function.uncurry X)
  apply stronglyMeasurable_of_tendsto atTop
    (fun n : ℕ ↦ (ha.measurable_strictLeftGrid_sample
      (show 0 < (1 : ℝ≥0) / ((n : ℝ≥0) + 1) from by positivity)).stronglyMeasurable)
  apply tendsto_pi_nhds.mpr
  intro z
  exact (hc z.2 z.1).tendsto.comp (tendsto_strictLeftGrid z.1)

theorem Adapted.exists_predictable_indistinguishable_of_hasLeftContinuousPaths
    (ha : Adapted F X) (hF : F.IsUsual P) (hc : HasLeftContinuousPaths X P) :
    ∃ Y : ℝ≥0 → Ω → ℝ, Indistinguishable X Y P ∧ IsStronglyPredictable F Y ∧
      ∀ ω, IsLeftContinuousPath (fun t ↦ Y t ω) := by
  classical
  let bad := {ω | ¬ IsLeftContinuousPath (fun t ↦ X t ω)}
  have hbad : MeasurableSet[F 0] bad := hF.complete_initial bad (ae_iff.mp hc)
  let Y : ℝ≥0 → Ω → ℝ := fun t ω ↦ if ω ∈ bad then 0 else X t ω
  have hYa : Adapted F Y := fun t ↦
    Measurable.ite (F.mono bot_le _ hbad) measurable_const (ha t)
  have hYc : ∀ ω, IsLeftContinuousPath (fun t ↦ Y t ω) := by
    intro ω
    by_cases hb : ω ∈ bad
    · simp only [Y, if_pos hb]
      exact fun _ ↦ continuousWithinAt_const
    · simpa only [Y, if_neg hb] using
        (not_not.mp hb : IsLeftContinuousPath (fun t ↦ X t ω))
  refine ⟨Y, ?_, hYa.isStronglyPredictable_of_leftContinuous hYc, hYc⟩
  filter_upwards [hc] with ω hω t
  exact (if_neg (show ω ∉ bad from fun hb ↦ hb hω)).symm

theorem Adapted.isStronglyPredictable_leftLimitProcess_of_cadlag (ha : Adapted F X)
    (hc : ∀ ω, IsCadlagPath (fun t ↦ X t ω)) :
    IsStronglyPredictable F (leftLimitProcess X) :=
  (ha.leftLimitProcess_of_cadlag hc).isStronglyPredictable_of_leftContinuous
    (fun ω ↦ (hc ω).isCagladPath_leftLimitProcess.1)

theorem Adapted.exists_predictable_leftLimitProcess_of_usual (ha : Adapted F X)
    (hF : F.IsUsual P) (hc : HasCadlagPaths X P) :
    ∃ Y : ℝ≥0 → Ω → ℝ, Indistinguishable (leftLimitProcess X) Y P ∧
      IsStronglyPredictable F Y ∧ ∀ ω, IsLeftContinuousPath (fun t ↦ Y t ω) := by
  have hl := ha.leftLimitProcess_of_usual hF hc
  exact hl.exists_predictable_indistinguishable_of_hasLeftContinuousPaths hF
    hc.hasCagladPaths_leftLimitProcess.hasLeftContinuousPaths

end MeasureTheory
