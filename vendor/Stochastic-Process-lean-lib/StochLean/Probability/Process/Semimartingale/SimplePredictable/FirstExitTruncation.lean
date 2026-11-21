/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.Stopping.LeftContinuousHitting
public import StochLean.Probability.Process.Semimartingale.SimplePredictable.Regularity
public import StochLean.Probability.Process.Semimartingale.SimplePredictable.InitialMask
public import StochLean.Probability.Process.Semimartingale.SimplePredictable.IntegralProcessStopping

/-! # Bounded source truncation at a left-continuous first exit

The initial event `{τ > 0}` is indispensable: the source class allows an arbitrary
initial value and a distinct right limit at zero. The closed cutoff is bounded by
the threshold on this event and its elementary integral agrees strictly before `τ`.
-/

@[expose] public section

open MeasureTheory Set
open scoped NNReal

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {F : Filtration ℝ≥0 mΩ}

/-- The source first-exit cutoff with the Protter initial-event mask. -/
noncomputable def firstExitTruncation (H : ℝ≥0 → Ω → ℝ) (a : ℝ) : ℝ≥0 → Ω → ℝ :=
  fun t ↦ {ω | (0 : WithTop ℝ≥0) < hittingAfter H {x | a < ‖x‖} 0 ω}.indicator
    (cutoffIntegrand H (hittingAfter H {x | a < ‖x‖} 0) t)

namespace IsSimplePredictable

variable {H : ℝ≥0 → Ω → ℝ}

theorem norm_firstExitTruncation_le (hH : IsSimplePredictable H F)
    {a : ℝ} (ha : 0 ≤ a) (t : ℝ≥0) (ω : Ω) : ‖firstExitTruncation H a t ω‖ ≤ a := by
  classical
  by_cases hpos : (0 : WithTop ℝ≥0) < hittingAfter H {x | a < ‖x‖} 0 ω
  · rw [firstExitTruncation, indicator_of_mem
      (show ω ∈ {v | (0 : WithTop ℝ≥0) < hittingAfter H {x | a < ‖x‖} 0 v} from hpos)]
    by_cases ht : (t : WithTop ℝ≥0) ≤ hittingAfter H {x | a < ‖x‖} 0 ω
    · simp only [cutoffIntegrand, if_pos ht]
      exact norm_le_of_le_hittingAfter_norm_of_pos (hH.isCagladPath ω).1 hpos ht
    · simpa only [cutoffIntegrand, if_neg ht, norm_zero] using ha
  · simpa only [firstExitTruncation, indicator_of_notMem
      (show ω ∉ {v | (0 : WithTop ℝ≥0) < hittingAfter H {x | a < ‖x‖} 0 v} from hpos),
      norm_zero] using ha

variable [F.IsRightContinuous]

theorem isStoppingTime_firstExit (hH : IsSimplePredictable H F) (a : ℝ) :
    IsStoppingTime F (hittingAfter H {x | a < ‖x‖} 0) :=
  hH.adapted.isStoppingTime_hittingAfter_isOpen_of_leftContinuous
    (fun ω ↦ (hH.isCagladPath ω).1) (isOpen_lt continuous_const continuous_norm) 0

theorem firstExitTruncation (hH : IsSimplePredictable H F) (a : ℝ) :
    IsSimplePredictable (ProbabilityTheory.firstExitTruncation H a) F :=
  (hH.cutoff (hH.isStoppingTime_firstExit a)).indicator
    ((hH.isStoppingTime_firstExit a).measurableSet_gt 0)

theorem elementaryIntegralProcess_firstExitTruncation (hH : IsSimplePredictable H F)
    (a : ℝ) (X : ℝ≥0 → Ω → ℝ) :
    (hH.firstExitTruncation a).elementaryIntegralProcess X =
      fun t ↦ {ω | (0 : WithTop ℝ≥0) < hittingAfter H {x | a < ‖x‖} 0 ω}.indicator
        (stoppedProcess (hH.elementaryIntegralProcess X) (hittingAfter H {x | a < ‖x‖} 0) t) := by
  change ((hH.cutoff (hH.isStoppingTime_firstExit a)).indicator
    ((hH.isStoppingTime_firstExit a).measurableSet_gt 0)).elementaryIntegralProcess X = _
  rw [(hH.cutoff (hH.isStoppingTime_firstExit a)).elementaryIntegralProcess_indicator
      ((hH.isStoppingTime_firstExit a).measurableSet_gt 0) X,
    hH.elementaryIntegralProcess_cutoff (hH.isStoppingTime_firstExit a) X]
  rfl

theorem elementaryIntegralProcess_firstExitTruncation_eq_of_lt
    (hH : IsSimplePredictable H F) (a : ℝ) (X : ℝ≥0 → Ω → ℝ) {t : ℝ≥0} {ω : Ω}
    (ht : (t : WithTop ℝ≥0) < hittingAfter H {x | a < ‖x‖} 0 ω) :
    (hH.firstExitTruncation a).elementaryIntegralProcess X t ω =
      hH.elementaryIntegralProcess X t ω := by
  have hp : (0 : WithTop ℝ≥0) < hittingAfter H {x | a < ‖x‖} 0 ω :=
    (show (0 : WithTop ℝ≥0) ≤ (t : WithTop ℝ≥0) from WithTop.coe_le_coe.mpr bot_le).trans_lt ht
  rw [hH.elementaryIntegralProcess_firstExitTruncation a X]
  change {v | (0 : WithTop ℝ≥0) < hittingAfter H {x | a < ‖x‖} 0 v}.indicator
    (stoppedProcess (hH.elementaryIntegralProcess X) (hittingAfter H {x | a < ‖x‖} 0) t) ω = _
  rw [indicator_of_mem
    (show ω ∈ {v | (0 : WithTop ℝ≥0) < hittingAfter H {x | a < ‖x‖} 0 v} from hp)]
  exact stoppedProcess_eq_of_le ht.le

end IsSimplePredictable
end ProbabilityTheory
