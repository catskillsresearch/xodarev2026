/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Analysis.PathVariation.LeftStepApproximation

/-! # Arbitrarily tagged step approximations

Tags may be either endpoint or any point between. They need not be ordered
separately from their containing cells; repeated partition endpoints are allowed.
-/

@[expose] public section

open Filter Set
open scoped NNReal Topology

namespace StochLean.TimePartition

variable {T : ℝ≥0}

noncomputable def taggedStep (π : TimePartition T) (ξ : Fin π.size → ℝ≥0)
    (f : ℝ≥0 → ℝ) (t : ℝ≥0) : ℝ :=
  if t = 0 then f 0 else
    ∑ i : Fin π.size, (Ioc (π.left i) (π.right i)).indicator (fun _ ↦ f (ξ i)) t

@[simp] theorem taggedStep_zero (π : TimePartition T) (ξ : Fin π.size → ℝ≥0) (f : ℝ≥0 → ℝ) :
    π.taggedStep ξ f 0 = f 0 := by simp only [taggedStep, ↓reduceIte]

theorem taggedStep_left (π : TimePartition T) (f : ℝ≥0 → ℝ) :
    π.taggedStep π.left f = π.leftStep f := rfl

theorem taggedStep_eq_of_mem_cell (π : TimePartition T) (ξ : Fin π.size → ℝ≥0)
    (f : ℝ≥0 → ℝ) {t : ℝ≥0} {i : Fin π.size}
    (hi : π.left i < t ∧ t ≤ π.right i) : π.taggedStep ξ f t = f (ξ i) := by
  have ht : t ≠ 0 := ne_of_gt (lt_of_le_of_lt bot_le hi.1)
  rw [taggedStep, if_neg ht, Finset.sum_eq_single i]
  · exact indicator_of_mem (s := Ioc (π.left i) (π.right i)) (a := t) hi (fun _ ↦ f (ξ i))
  · intro j _ hji
    apply indicator_of_notMem
    intro hj
    exact hji (π.cell_unique hj hi)
  · simp only [Finset.mem_univ, not_true_eq_false, false_implies]

theorem dist_tag_of_mem_cell_le_mesh (π : TimePartition T) (ξ : Fin π.size → ℝ≥0)
    (hξ : ∀ i, π.left i ≤ ξ i ∧ ξ i ≤ π.right i) {t : ℝ≥0} {i : Fin π.size}
    (hi : π.left i < t ∧ t ≤ π.right i) : dist t (ξ i) ≤ (π.mesh : ℝ) := by
  have htl : (π.left i : ℝ) ≤ t := by exact_mod_cast hi.1.le
  have htr : (t : ℝ) ≤ π.right i := by exact_mod_cast hi.2
  have hξl : (π.left i : ℝ) ≤ ξ i := by exact_mod_cast (hξ i).1
  have hξr : (ξ i : ℝ) ≤ π.right i := by exact_mod_cast (hξ i).2
  calc
    dist t (ξ i) ≤ (π.right i : ℝ) - π.left i := by
      rw [NNReal.dist_eq, abs_le]
      constructor <;> linarith
    _ = (π.gap i : ℝ) := (NNReal.coe_sub (π.left_le_right i)).symm
    _ ≤ π.mesh := by exact_mod_cast π.gap_le_mesh i

theorem tendstoUniformlyOn_taggedStep {π : ℕ → TimePartition T}
    (ξ : ∀ n, Fin (π n).size → ℝ≥0)
    (hξ : ∀ n i, (π n).left i ≤ ξ n i ∧ ξ n i ≤ (π n).right i)
    {f : ℝ≥0 → ℝ} (hf : ContinuousOn f (Icc 0 T))
    (hmesh : Tendsto (fun n ↦ ((π n).mesh : ℝ)) atTop (𝓝 0)) :
    TendstoUniformlyOn (fun n ↦ (π n).taggedStep (ξ n) f) f atTop (Icc 0 T) := by
  apply Metric.tendstoUniformlyOn_iff.mpr
  intro ε hε
  obtain ⟨δ, hδ, hmod⟩ := Metric.uniformContinuousOn_iff.mp
    (isCompact_Icc.uniformContinuousOn_of_continuous hf) ε hε
  filter_upwards [hmesh.eventually_lt_const hδ] with n hn
  intro t ht
  by_cases ht0 : t = 0
  · subst t
    simpa only [taggedStep_zero, dist_self] using hε
  · obtain ⟨i, hi⟩ := (π n).exists_cell ⟨lt_of_le_of_ne bot_le (Ne.symm ht0), ht.2⟩
    rw [(π n).taggedStep_eq_of_mem_cell (ξ n) f hi]
    exact hmod t ht (ξ n i) ⟨bot_le, (hξ n i).2.trans ((π n).point_le_horizon _)⟩
      (((π n).dist_tag_of_mem_cell_le_mesh (ξ n) (hξ n) hi).trans_lt hn)

end StochLean.TimePartition
