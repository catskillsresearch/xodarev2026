/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.Stopping.Announcing
public import Mathlib.Analysis.SpecificLimits.Basic

/-! # Deterministic announcing sequences, including zero and infinity -/

@[expose] public section

open MeasureTheory Filter
open scoped NNReal Topology

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

theorem isAnnouncingSequence_const (F : Filtration ℝ≥0 mΩ) (P : Measure Ω) (t : ℝ≥0) :
    IsAnnouncingSequence F P (fun _ ↦ (t : WithTop ℝ≥0))
      (fun n _ ↦ ((t - 1 / ((n : ℝ≥0) + 1) : ℝ≥0) : WithTop ℝ≥0)) := by
  refine ⟨fun n ↦ isStoppingTime_const F _, fun _ i j hij ↦ ?_, fun n _ ht ↦ ?_, ?_⟩
  · apply WithTop.coe_le_coe.mpr
    apply tsub_le_tsub_left
    apply one_div_le_one_div_of_le (by positivity)
    exact add_le_add (Nat.cast_le.mpr hij) le_rfl
  · apply WithTop.coe_lt_coe.mpr
    exact tsub_lt_self (WithTop.coe_lt_coe.mp ht) (by positivity)
  · apply Eventually.of_forall
    intro _
    have hl : Tendsto (fun n : ℕ ↦ t - 1 / ((n : ℝ≥0) + 1)) atTop (𝓝 t) := by
      simpa only [tsub_zero] using
        tendsto_const_nhds.sub (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ≥0))
    exact WithTop.continuous_coe.continuousAt.tendsto.comp hl

theorem isPredictableStoppingTime_const (F : Filtration ℝ≥0 mΩ) (P : Measure Ω) (t : ℝ≥0) :
    IsPredictableStoppingTime F (fun _ ↦ (t : WithTop ℝ≥0)) P :=
  (isAnnouncingSequence_const F P t).predictable (isStoppingTime_const F t)

theorem isAnnouncingSequence_top (F : Filtration ℝ≥0 mΩ) (P : Measure Ω) :
    IsAnnouncingSequence F P (fun _ ↦ ⊤)
      (fun n _ ↦ ((n : ℝ≥0) : WithTop ℝ≥0)) := by
  refine ⟨fun n ↦ isStoppingTime_const F _, fun _ i j hij ↦ ?_,
    fun n _ _ ↦ WithTop.coe_lt_top _, ?_⟩
  · exact WithTop.coe_le_coe.mpr (Nat.cast_le.mpr hij)
  · exact Eventually.of_forall fun _ ↦ WithTop.tendsto_coe_atTop.comp
      (tendsto_natCast_atTop_atTop (R := ℝ≥0))

theorem isPredictableStoppingTime_top (F : Filtration ℝ≥0 mΩ) (P : Measure Ω) :
    IsPredictableStoppingTime F (fun _ ↦ ⊤) P :=
  (isAnnouncingSequence_top F P).predictable (fun _ ↦ by simp)

end ProbabilityTheory
