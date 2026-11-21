/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.Semimartingale.SimplePredictable.IntegralProcess

/-! # The elementary integral increment on one source partition cell

Earlier cells have already finished, later cells have not started, and the
current coefficient multiplies precisely the integrator increment. Repeated
endpoints are retained: their increment is zero, whatever the coefficient.
-/

@[expose] public section

open MeasureTheory Finset
open scoped NNReal

namespace ProbabilityTheory.SimplePredictableRep

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {F : Filtration ℝ≥0 mΩ}

theorem integralProcess_increment_cell (H : SimplePredictableRep F)
    (X : ℝ≥0 → Ω → ℝ) (i : Fin H.partition.size) (ω : Ω) :
    H.integralProcess X (H.partition.point i.succ ω) ω -
        H.integralProcess X (H.partition.point i.castSucc ω) ω =
      H.coefficient i ω * (X (H.partition.point i.succ ω) ω -
        X (H.partition.point i.castSucc ω) ω) := by
  have hi : H.partition.point i.castSucc ω ≤ H.partition.point i.succ ω :=
    H.partition.monotone_point ω (Fin.castSucc_le_succ i)
  rw [integralProcess_apply, integralProcess_apply, add_sub_add_left_eq_sub,
    ← Finset.sum_sub_distrib, Finset.sum_eq_single i]
  · simp only [min_self, min_eq_left hi, min_eq_right hi, sub_self, mul_zero, sub_zero]
  · intro j _ hji
    have hj : H.partition.point j.castSucc ω ≤ H.partition.point j.succ ω :=
      H.partition.monotone_point ω (Fin.castSucc_le_succ j)
    rcases lt_or_gt_of_ne hji with hlt | hgt
    · have hbefore : H.partition.point j.succ ω ≤ H.partition.point i.castSucc ω :=
        H.partition.monotone_point ω (Fin.succ_le_castSucc_iff.mpr hlt)
      simp only [min_eq_left hbefore, min_eq_left (hj.trans hbefore),
        min_eq_left (hbefore.trans hi), min_eq_left ((hj.trans hbefore).trans hi), sub_self]
    · have hafter : H.partition.point i.succ ω ≤ H.partition.point j.castSucc ω :=
        H.partition.monotone_point ω (Fin.succ_le_castSucc_iff.mpr hgt)
      simp only [min_eq_right hafter, min_eq_right (hafter.trans hj),
        min_eq_right (hi.trans hafter), min_eq_right (hi.trans (hafter.trans hj)),
        sub_self, mul_zero]
  · simp

end ProbabilityTheory.SimplePredictableRep
