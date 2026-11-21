/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Analysis.PathVariation.Stieltjes
public import Mathlib.Analysis.Real.Sqrt

/-! # From a covariation increment bound to a total-variation bound

Finite ordered variation sums satisfy Cauchy--Schwarz, and taking their
supremum gives the interval bound for the canonical variation measure.
The paths may jump. The result concerns increment measures; no atom is
silently inserted at the initial endpoint.
-/

@[expose] public section

open Set Filter MeasureTheory Finset
open scoped NNReal ENNReal Topology

namespace StochLean

variable {α : Type*} [LinearOrder α] {a b c : α → ℝ}

theorem eVariationOn_le_of_covariation_increment_bound
    (hb : Monotone b) (hc : Monotone c)
    (ha : ∀ s t, s ≤ t → |a t - a s| ≤ Real.sqrt (b t - b s) * Real.sqrt (c t - c s))
    (s t : α) :
    eVariationOn a (Icc s t) ≤ ENNReal.ofReal (Real.sqrt (b t - b s) * Real.sqrt (c t - c s)) := by
  apply iSup_le
  rintro ⟨n, ⟨u, hu, hus⟩⟩
  have hsum : (∑ i ∈ range n, |a (u (i + 1)) - a (u i)|) ≤
      Real.sqrt (b (u n) - b (u 0)) * Real.sqrt (c (u n) - c (u 0)) := by
    calc
      _ ≤ ∑ i ∈ range n,
          Real.sqrt (b (u (i + 1)) - b (u i)) * Real.sqrt (c (u (i + 1)) - c (u i)) :=
        sum_le_sum fun i _ ↦ ha _ _ (hu (Nat.le_succ i))
      _ ≤ Real.sqrt (∑ i ∈ range n, (b (u (i + 1)) - b (u i))) *
          Real.sqrt (∑ i ∈ range n, (c (u (i + 1)) - c (u i))) :=
        Real.sum_sqrt_mul_sqrt_le (range n)
          (fun i ↦ sub_nonneg.mpr (hb (hu (Nat.le_succ i))))
          (fun i ↦ sub_nonneg.mpr (hc (hu (Nat.le_succ i))))
      _ = _ := by rw [sum_range_sub (fun i ↦ b (u i)), sum_range_sub (fun i ↦ c (u i))]
  calc
    _ = ENNReal.ofReal (∑ i ∈ range n, |a (u (i + 1)) - a (u i)|) := by
      simp only [edist_dist, Real.dist_eq]
      rw [ENNReal.ofReal_sum_of_nonneg (fun i _ ↦ abs_nonneg _)]
    _ ≤ ENNReal.ofReal
        (Real.sqrt (b (u n) - b (u 0)) * Real.sqrt (c (u n) - c (u 0))) :=
      ENNReal.ofReal_le_ofReal hsum
    _ ≤ _ := by
      apply ENNReal.ofReal_le_ofReal
      exact mul_le_mul
        (Real.sqrt_le_sqrt (sub_le_sub (hb (hus n).2) (hb (hus 0).1)))
        (Real.sqrt_le_sqrt (sub_le_sub (hc (hus n).2) (hc (hus 0).1)))
        (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)

theorem locallyBoundedVariationOn_of_covariation_increment_bound
    (hb : Monotone b) (hc : Monotone c)
    (ha : ∀ s t, s ≤ t → |a t - a s| ≤ Real.sqrt (b t - b s) * Real.sqrt (c t - c s)) :
    LocallyBoundedVariationOn a univ := by
  intro s t _ _
  simp only [univ_inter]
  exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top
    (eVariationOn_le_of_covariation_increment_bound hb hc ha s t)

theorem totalVariationStieltjes_measure_Ioc_le_of_covariation_increment_bound
    {a b c : ℝ≥0 → ℝ} (haBV : LocallyBoundedVariationOn a univ)
    (haRC : ∀ t, ContinuousWithinAt a (Ici t) t) (hb : Monotone b) (hc : Monotone c)
    (ha : ∀ s t, s ≤ t → |a t - a s| ≤ Real.sqrt (b t - b s) * Real.sqrt (c t - c s))
    {s t : ℝ≥0} (hst : s ≤ t) :
    (totalVariationStieltjes a haBV haRC).measure (Ioc s t) ≤
      ENNReal.ofReal (Real.sqrt (b t - b s) * Real.sqrt (c t - c s)) := by
  rw [totalVariationStieltjes_measure_Ioc a haBV haRC hst]
  exact eVariationOn_le_of_covariation_increment_bound hb hc ha s t

end StochLean
