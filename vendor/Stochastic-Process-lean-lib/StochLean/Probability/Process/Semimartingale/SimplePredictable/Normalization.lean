/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.Semimartingale.SimplePredictable

/-! # Removing irrelevant coefficients on zero-length stopping intervals

A bounded simple process can have unbounded representation coefficients on empty intervals.
Set those coefficients to zero before using a coefficient-wise martingale estimate. The process
and its elementary integral are unchanged, and measurability is retained at the left endpoint.
-/

@[expose] public section

open MeasureTheory Finset Set
open scoped NNReal

namespace ProbabilityTheory.SimplePredictableRep

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {F : Filtration ℝ≥0 mΩ}

theorem toProcess_rightEndpoint (H : SimplePredictableRep F) (i : Fin H.partition.size)
    {ω : Ω} (hi : H.partition.point i.castSucc ω < H.partition.point i.succ ω) :
    H.toProcess (H.partition.point i.succ ω) ω = H.coefficient i ω := by
  have hpos : 0 < H.partition.point i.succ ω := lt_of_le_of_lt bot_le hi
  rw [toProcess, if_neg (ne_of_gt hpos)]
  rw [sum_eq_single i]
  · simp only [hi, le_refl, and_self, if_true]
  · intro j _ hji
    rcases lt_or_gt_of_ne hji with hji | hij
    · have hle : H.partition.point j.succ ω ≤ H.partition.point i.castSucc ω :=
        H.partition.monotone_point ω (show j.succ ≤ i.castSucc from hji)
      exact if_neg (fun h ↦ (not_le.mpr (hle.trans_lt hi)) h.2)
    · have hle : H.partition.point i.succ ω ≤ H.partition.point j.castSucc ω :=
        H.partition.monotone_point ω (show i.succ ≤ j.castSucc from hij)
      exact if_neg (fun h ↦ (not_lt.mpr hle) h.1)
  · simp

theorem measurableSet_strictInterval (H : SimplePredictableRep F) (i : Fin H.partition.size) :
    MeasurableSet[(H.partition.point i.castSucc).measurableSpace]
      {ω | H.partition.point i.castSucc ω < H.partition.point i.succ ω} := by
  simpa only [Set.compl_ofPred, WithTop.coe_le_coe, not_le] using
    ((H.partition.point i.succ).isStoppingTime.measurableSet_stopping_time_le
      (H.partition.point i.castSucc).isStoppingTime).compl

/-- Normalize only coefficients on empty intervals; the source permits these unbounded
coefficients, so bounding them must be a proved reduction, not an added assumption. -/
noncomputable def removeEmptyIntervals (H : SimplePredictableRep F) : SimplePredictableRep F where
  partition := H.partition
  initial := H.initial
  measurable_initial := H.measurable_initial
  coefficient := fun i ↦
    {ω | H.partition.point i.castSucc ω < H.partition.point i.succ ω}.indicator (H.coefficient i)
  measurable_coefficient := fun i ↦
    (H.measurable_coefficient i).indicator (H.measurableSet_strictInterval i)

theorem toProcess_removeEmptyIntervals (H : SimplePredictableRep F) :
    H.removeEmptyIntervals.toProcess = H.toProcess := by
  funext t ω
  by_cases ht : t = 0
  · subst t
    simp only [toProcess_zero]
    rfl
  change (if t = 0 then H.initial ω else ∑ i : Fin H.partition.size,
    if H.partition.point i.castSucc ω < t ∧ t ≤ H.partition.point i.succ ω then
      {ω | H.partition.point i.castSucc ω < H.partition.point i.succ ω}.indicator
        (H.coefficient i) ω else 0) = H.toProcess t ω
  simp only [toProcess, if_neg ht]
  apply sum_congr rfl
  intro i _
  by_cases hi : H.partition.point i.castSucc ω < t ∧ t ≤ H.partition.point i.succ ω
  · rw [if_pos hi, if_pos hi, indicator_of_mem
      (show ω ∈ {ω | H.partition.point i.castSucc ω < H.partition.point i.succ ω}
        from hi.1.trans_le hi.2)]
  · simp only [if_neg hi]

theorem integral_removeEmptyIntervals (H : SimplePredictableRep F) (X : ℝ≥0 → Ω → ℝ) :
    H.removeEmptyIntervals.integral X = H.integral X :=
  H.removeEmptyIntervals.integral_congr H H.toProcess_removeEmptyIntervals X

theorem norm_coefficient_removeEmptyIntervals_le (H : SimplePredictableRep F) {C : ℝ}
    (hC : 0 ≤ C) (hb : ∀ t ω, ‖H.toProcess t ω‖ ≤ C)
    (i : Fin H.partition.size) (ω : Ω) : ‖H.removeEmptyIntervals.coefficient i ω‖ ≤ C := by
  change ‖{ω | H.partition.point i.castSucc ω < H.partition.point i.succ ω}.indicator
    (H.coefficient i) ω‖ ≤ C
  by_cases hi : H.partition.point i.castSucc ω < H.partition.point i.succ ω
  · rw [indicator_of_mem (show ω ∈ {ω | H.partition.point i.castSucc ω <
      H.partition.point i.succ ω} from hi), ← H.toProcess_rightEndpoint i hi]
    exact hb _ ω
  · rw [indicator_of_notMem (show ω ∉ {ω | H.partition.point i.castSucc ω <
      H.partition.point i.succ ω} from hi), norm_zero]
    exact hC

end ProbabilityTheory.SimplePredictableRep
