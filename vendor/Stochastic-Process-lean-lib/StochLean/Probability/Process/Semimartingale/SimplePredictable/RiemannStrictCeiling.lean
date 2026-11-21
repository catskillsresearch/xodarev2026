/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.Partition.LeftSampling
public import StochLean.Analysis.PathVariation.LeftStepStrictCeiling

/-! # Exact random Riemann sums of full source simple processes

The separate initial coefficient contributes on the first positive sampling
cell. The positive-time `Ioc` steps move to strictly upper sampling endpoints.
-/

@[expose] public section

open MeasureTheory Finset
open scoped NNReal

namespace ProbabilityTheory.SimplePredictableRep

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {F : Filtration ℝ≥0 mΩ}

theorem toProcess_eq_initial_spike_add_sum (H : SimplePredictableRep F)
    (t : ℝ≥0) (ω : Ω) :
    H.toProcess t ω = (if t = 0 then H.initial ω else 0) +
      ∑ i : Fin H.partition.size,
        if H.partition.point i.castSucc ω < t ∧ t ≤ H.partition.point i.succ ω
        then H.coefficient i ω else 0 := by
  by_cases ht : t = 0
  · subst t
    simp only [toProcess_zero, not_lt_zero, false_and,
      Finset.sum_const_zero, ↓reduceIte, add_zero]
  · simp only [toProcess, if_neg ht, zero_add]

theorem leftRiemannSum_toProcess (H : SimplePredictableRep F)
    (π : StoppingTimePartition F) (X : ℝ≥0 → Ω → ℝ) (t : ℝ≥0) (ω : Ω) :
    π.leftRiemannSumProcess H.toProcess X t ω =
      H.initial ω * (X (min ((π.path ω).strictCeilingPoint 0) t) ω - X 0 ω) +
      ∑ j : Fin H.partition.size, H.coefficient j ω *
        (X (min ((π.path ω).strictCeilingPoint (H.partition.point j.succ ω)) t) ω -
          X (min ((π.path ω).strictCeilingPoint (H.partition.point j.castSucc ω)) t) ω) := by
  unfold StoppingTimePartition.leftRiemannSumProcess
  simp_rw [H.toProcess_eq_initial_spike_add_sum, add_mul, Finset.sum_add_distrib]
  congr 1
  · convert! (π.path ω).sum_increment_initial_spike (H.initial ω)
      (fun u ↦ X (min u t) ω) using 1
    simp only [zero_min]
  · simp_rw [Finset.sum_mul]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j _
    exact (π.path ω).sum_increment_step_Ioc ((H.partition.path ω).left_le_right j)
      (H.coefficient j ω) (fun u ↦ X (min u t) ω)

end ProbabilityTheory.SimplePredictableRep
