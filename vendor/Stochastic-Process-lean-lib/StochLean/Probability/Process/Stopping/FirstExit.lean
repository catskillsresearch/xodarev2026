/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.Stopping.RightContinuousHitting

/-! # Norm bounds at a right-continuous first exit

Strictly before the first exit the norm is at most the threshold. At a finite
first exit the norm is at least the threshold; jumps may overshoot it. No equality
or upper bound at the stopping endpoint is asserted without additional continuity.
-/

@[expose] public section

open MeasureTheory Filter Set
open scoped NNReal Topology

namespace MeasureTheory

variable {Ω : Type*} {X : ℝ≥0 → Ω → ℝ}

theorem norm_le_of_lt_hittingAfter_norm {a : ℝ} {t : ℝ≥0} {ω : Ω}
    (ht : (t : WithTop ℝ≥0) < hittingAfter X {x | a < ‖x‖} 0 ω) : ‖X t ω‖ ≤ a := by
  have hnot : X t ω ∉ {x : ℝ | a < ‖x‖} :=
    notMem_of_lt_hittingAfter (u := X) (s := {x | a < ‖x‖}) ht
      (bot_le : (0 : ℝ≥0) ≤ t)
  exact le_of_not_gt hnot

theorem le_norm_hittingAfter_norm_of_ne_top {a : ℝ} {ω : Ω}
    (hr : ProbabilityTheory.IsRightContinuousPath (X · ω))
    (hne : hittingAfter X {x | a < ‖x‖} 0 ω ≠ ⊤) :
    a ≤ ‖X (hittingAfter X {x | a < ‖x‖} 0 ω).untopA ω‖ := by
  have hmem := hittingAfter_mem_closure_of_rightContinuous hr hne
  have hsub : {x : ℝ | a < ‖x‖} ⊆ {x | a ≤ ‖x‖} := by
    intro x hx
    exact (show a < ‖x‖ from hx).le
  have hs : closure {x : ℝ | a < ‖x‖} ⊆ {x | a ≤ ‖x‖} :=
    closure_minimal hsub (isClosed_le continuous_const continuous_norm)
  exact hs hmem

variable {mΩ : MeasurableSpace Ω} {F : Filtration ℝ≥0 mΩ} {P : Measure Ω}

theorem Adapted.isStoppingTime_hittingAfter_norm [F.IsRightContinuous]
    (hX : Adapted F X) (hr : ∀ ω, ProbabilityTheory.IsRightContinuousPath (X · ω))
    (a : ℝ) : IsStoppingTime F (hittingAfter X {x | a < ‖x‖} 0) :=
  hX.isStoppingTime_hittingAfter_isOpen hr (isOpen_lt continuous_const continuous_norm) 0

theorem Adapted.isStoppingTime_hittingAfter_norm_of_usual
    (hX : Adapted F X) (hF : F.IsUsual P)
    (hr : ProbabilityTheory.HasRightContinuousPaths X P) (a : ℝ) :
    IsStoppingTime F (hittingAfter X {x | a < ‖x‖} 0) :=
  hX.isStoppingTime_hittingAfter_isOpen_of_usual hF hr
    (isOpen_lt continuous_const continuous_norm) 0

theorem ae_le_norm_hittingAfter_norm_of_ne_top
    (hr : ProbabilityTheory.HasRightContinuousPaths X P) (a : ℝ) :
    ∀ᵐ ω ∂P, hittingAfter X {x | a < ‖x‖} 0 ω ≠ ⊤ →
      a ≤ ‖X (hittingAfter X {x | a < ‖x‖} 0 ω).untopA ω‖ :=
  hr.mono fun _ hω hne ↦ le_norm_hittingAfter_norm_of_ne_top hω hne

end MeasureTheory
