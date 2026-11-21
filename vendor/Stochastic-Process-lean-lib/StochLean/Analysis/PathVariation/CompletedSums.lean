/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Analysis.PathVariation.FiniteVariation
public import StochLean.Analysis.PathVariation.Algebra

/-!
# Completed-cell variation sums

Completed square sums, unlike sums with a moving partial terminal cell, are
monotone in time. Their covariation analogue has total variation bounded by
the sum of the absolute increment products. This is the deterministic repair
required for Klenke 21.71, and the variation estimate behind Remark 21.61(ii).
-/

@[expose] public section

open Filter Finset Set
open scoped NNReal ENNReal Topology

namespace StochLean

/-- Cumulative sum of finitely many jumps. The event includes the jump time. -/
noncomputable def cumulativeStepSum {ι : Type*} [Fintype ι]
    (a : ι → ℝ≥0) (c : ι → ℝ) (t : ℝ≥0) : ℝ :=
  ∑ i, if a i ≤ t then c i else 0

theorem cumulativeStepSum_mono {ι : Type*} [Fintype ι]
    (a : ι → ℝ≥0) {c : ι → ℝ} (hc : ∀ i, 0 ≤ c i) :
    Monotone (cumulativeStepSum a c) := by
  intro s t hst
  apply sum_le_sum
  intro i _
  by_cases hs : a i ≤ s
  · simp [hs, hs.trans hst]
  · simp only [hs, ↓reduceIte]
    split_ifs <;> simp [hc]

theorem eVariationOn_cumulativeStepSum_le {ι : Type*} [Fintype ι]
    (a : ι → ℝ≥0) (c : ι → ℝ) (s : Set ℝ≥0) :
    eVariationOn (cumulativeStepSum a c) s ≤ ENNReal.ofReal (∑ i, |c i|) := by
  classical
  let V := cumulativeStepSum a (fun i ↦ |c i|)
  have hVnonneg (t : ℝ≥0) : 0 ≤ V t := by
    apply sum_nonneg
    intro i _
    split_ifs <;> simp
  have hVle (t : ℝ≥0) : V t ≤ ∑ i, |c i| := by
    apply sum_le_sum
    intro i _
    split_ifs <;> simp
  have hdist {x y : ℝ≥0} (hxy : x ≤ y) :
      dist (cumulativeStepSum a c y) (cumulativeStepSum a c x) ≤ V y - V x := by
    rw [Real.dist_eq, cumulativeStepSum, cumulativeStepSum, ← sum_sub_distrib]
    apply (abs_sum_le_sum_abs _ _).trans
    change (∑ i, |(if a i ≤ y then c i else 0) - (if a i ≤ x then c i else 0)|) ≤
      (∑ i, if a i ≤ y then |c i| else 0) - ∑ i, if a i ≤ x then |c i| else 0
    rw [← sum_sub_distrib]
    apply sum_le_sum
    intro i _
    by_cases hx : a i ≤ x
    · simp [hx, hx.trans hxy]
    · simp only [hx, ↓reduceIte, sub_zero]
      split_ifs <;> simp
  apply iSup_le
  rintro ⟨n, u, hu, _⟩
  simp only
  calc
    (∑ i ∈ range n, edist (cumulativeStepSum a c (u (i + 1)))
        (cumulativeStepSum a c (u i))) ≤
        ∑ i ∈ range n, ENNReal.ofReal (V (u (i + 1)) - V (u i)) := by
      apply sum_le_sum
      intro i _
      rw [edist_dist]
      exact ENNReal.ofReal_le_ofReal (hdist (hu (Nat.le_succ i)))
    _ = ENNReal.ofReal (V (u n) - V (u 0)) := by
      rw [← ENNReal.ofReal_sum_of_nonneg]
      · exact congrArg ENNReal.ofReal (sum_range_sub (fun k ↦ V (u k)) n)
      · intro i _
        exact sub_nonneg.mpr (cumulativeStepSum_mono a (fun i ↦ abs_nonneg (c i))
          (hu (Nat.le_succ i)))
    _ ≤ ENNReal.ofReal (∑ i, |c i|) :=
      ENNReal.ofReal_le_ofReal ((sub_le_self _ (hVnonneg _)).trans (hVle _))

variable {T : ℝ≥0}

noncomputable def completedQuadraticVariationSum (π : TimePartition T)
    (f : ℝ≥0 → ℝ) : ℝ≥0 → ℝ :=
  cumulativeStepSum π.right (fun i ↦ (π.increment f i) ^ 2)

noncomputable def completedCovariationSum (π : TimePartition T)
    (f g : ℝ≥0 → ℝ) : ℝ≥0 → ℝ :=
  cumulativeStepSum π.right (fun i ↦ π.increment f i * π.increment g i)

theorem completedQuadraticVariationSum_mono (π : TimePartition T) (f : ℝ≥0 → ℝ) :
    Monotone (completedQuadraticVariationSum π f) :=
  cumulativeStepSum_mono π.right (fun _ ↦ sq_nonneg _)

@[simp] theorem completedQuadraticVariationSum_horizon (π : TimePartition T) (f : ℝ≥0 → ℝ) :
    completedQuadraticVariationSum π f T = quadraticVariationSum π f := by
  simp only [completedQuadraticVariationSum, cumulativeStepSum, quadraticVariationSum,
    TimePartition.right, π.point_le_horizon, ↓reduceIte]

@[simp] theorem completedCovariationSum_horizon (π : TimePartition T) (f g : ℝ≥0 → ℝ) :
    completedCovariationSum π f g T = covariationSum π f g := by
  simp only [completedCovariationSum, cumulativeStepSum, covariationSum,
    TimePartition.right, π.point_le_horizon, ↓reduceIte]

theorem sum_abs_increment_mul_le (π : TimePartition T) (f g : ℝ≥0 → ℝ) :
    (∑ i, |π.increment f i * π.increment g i|) ≤
      Real.sqrt (quadraticVariationSum π f) * Real.sqrt (quadraticVariationSum π g) := by
  have h := sum_mul_sq_le_sq_mul_sq univ
    (fun i ↦ |π.increment f i|) (fun i ↦ |π.increment g i|)
  simp only [sq_abs, ← abs_mul] at h
  have h' := Real.le_sqrt_of_sq_le h
  change (∑ i, |π.increment f i * π.increment g i|) ≤
    Real.sqrt (quadraticVariationSum π f * quadraticVariationSum π g) at h'
  rwa [Real.sqrt_mul (quadraticVariationSum_nonneg π f)] at h'

theorem eVariationOn_completedCovariationSum_le (π : TimePartition T)
    (f g : ℝ≥0 → ℝ) (s : Set ℝ≥0) :
    eVariationOn (completedCovariationSum π f g) s ≤
      ENNReal.ofReal (Real.sqrt (quadraticVariationSum π f) *
        Real.sqrt (quadraticVariationSum π g)) :=
  (eVariationOn_cumulativeStepSum_le ..).trans
    (ENNReal.ofReal_le_ofReal (sum_abs_increment_mul_le π f g))

end StochLean
