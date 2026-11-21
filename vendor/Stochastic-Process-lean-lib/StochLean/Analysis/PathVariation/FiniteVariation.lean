/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Analysis.PathVariation.Oscillation
public import Mathlib.Topology.EMetricSpace.BoundedVariation
public import Mathlib.Topology.UniformSpace.HeineCantor
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Linarith

/-! # Continuous paths of bounded variation have zero increment quadratic variation -/

@[expose] public section

open Filter Finset Set
open scoped NNReal ENNReal Topology BigOperators

namespace StochLean

variable {T : ℝ≥0}

theorem TimePartition.sum_enorm_increment_le (π : TimePartition T) (f : ℝ≥0 → ℝ) :
    (∑ i, ENNReal.ofReal |π.increment f i|) ≤ eVariationOn f (Icc 0 T) := by
  let u : ℕ → ℝ≥0 := fun n ↦ π.point ⟨min n π.size, Nat.lt_succ_of_le (min_le_right _ _)⟩
  have hu : Monotone u := fun n m hnm ↦ π.monotone_point (by
    change min n π.size ≤ min m π.size
    exact min_le_min_right _ hnm)
  have hmem : ∀ n, u n ∈ Icc 0 T := fun n ↦ ⟨bot_le, π.point_le_horizon _⟩
  have hsum := eVariationOn.sum_le (n := π.size) (f := f) hu hmem
  rw [Finset.sum_range] at hsum
  convert hsum using 1
  apply Finset.sum_congr rfl
  intro i _
  have h₀ : u i = π.left i := by
    simp only [u, TimePartition.left, min_eq_left i.isLt.le]
    exact congrArg π.point (Fin.ext rfl)
  have h₁ : u (i + 1) = π.right i := by
    simp only [u, TimePartition.right, min_eq_left (Nat.succ_le_of_lt i.isLt)]
    exact congrArg π.point (Fin.ext rfl)
  rw [h₀, h₁, edist_dist, Real.dist_eq, TimePartition.increment]

theorem TimePartition.sum_abs_increment_le (π : TimePartition T) {f : ℝ≥0 → ℝ}
    (hf : BoundedVariationOn f (Icc 0 T)) :
    (∑ i, |π.increment f i|) ≤ (eVariationOn f (Icc 0 T)).toReal := by
  apply (ENNReal.ofReal_le_iff_le_toReal hf).mp
  rw [ENNReal.ofReal_sum_of_nonneg (fun i _ ↦ abs_nonneg _)]
  exact π.sum_enorm_increment_le f

theorem quadraticVariationSum_le_maxIncrement_mul_variation (π : TimePartition T)
    {f : ℝ≥0 → ℝ} (hf : BoundedVariationOn f (Icc 0 T)) {δ : ℝ} (hδ : 0 ≤ δ)
    (hinc : ∀ i, |π.increment f i| ≤ δ) :
    quadraticVariationSum π f ≤ δ * (eVariationOn f (Icc 0 T)).toReal := by
  calc
    quadraticVariationSum π f = ∑ i, |π.increment f i| * |π.increment f i| := by
      simp only [quadraticVariationSum, ← pow_two, sq_abs]
    _ ≤ ∑ i, δ * |π.increment f i| :=
      sum_le_sum fun i _ ↦ mul_le_mul_of_nonneg_right (hinc i) (abs_nonneg _)
    _ = δ * ∑ i, |π.increment f i| := (mul_sum ..).symm
    _ ≤ δ * (eVariationOn f (Icc 0 T)).toReal :=
      mul_le_mul_of_nonneg_left (π.sum_abs_increment_le hf) hδ

/-- This result requires only vanishing mesh, not refinement or a summable rate. -/
theorem hasQuadraticVariationAlong_zero_of_continuous_boundedVariation
    {f : ℝ≥0 → ℝ} (hf : ContinuousOn f (Icc 0 T))
    (hfv : BoundedVariationOn f (Icc 0 T)) {π : ℕ → TimePartition T}
    (hmesh : Tendsto (fun n ↦ ((π n).mesh : ℝ)) atTop (𝓝 0)) :
    HasQuadraticVariationAlong π f 0 := by
  have huc := isCompact_Icc.uniformContinuousOn_of_continuous hf
  apply tendsto_order.mpr
  constructor
  · intro a ha
    exact Eventually.of_forall fun n ↦ ha.trans_le (quadraticVariationSum_nonneg (π n) f)
  · intro ε hε
    let V := (eVariationOn f (Icc 0 T)).toReal
    have hV : 0 ≤ V := ENNReal.toReal_nonneg
    have hδ : 0 < ε / (V + 1) := div_pos hε (by positivity)
    obtain ⟨η, hη, hmod⟩ := Metric.uniformContinuousOn_iff.mp huc _ hδ
    filter_upwards [hmesh.eventually_lt_const hη] with n hn
    have hinc : ∀ i, |(π n).increment f i| ≤ ε / (V + 1) := by
      intro i
      apply le_of_lt
      have hdist : dist ((π n).right i) ((π n).left i) < η := by
        rw [(π n).dist_right_left_eq_gap]
        exact (show ((π n).gap i : ℝ) ≤ ((π n).mesh : ℝ) by
          exact_mod_cast (π n).gap_le_mesh i).trans_lt hn
      exact hmod _ ⟨bot_le, (π n).point_le_horizon _⟩
        _ ⟨bot_le, (π n).point_le_horizon _⟩ hdist
    refine (quadraticVariationSum_le_maxIncrement_mul_variation (π n) hfv hδ.le hinc).trans_lt ?_
    change ε / (V + 1) * V < ε
    have hprod : ε / (V + 1) * (V + 1) = ε :=
      div_mul_cancel₀ ε (by positivity)
    nlinarith

end StochLean
