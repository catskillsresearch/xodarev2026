/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Analysis.PathVariation.ContinuousPairBounds

/-! # Quadratic endpoint-pair sums and vanishing continuous diagonal errors

The last partially traversed cell is included. Uniform control needs a bound
on the actual partial square sums, not monotonicity of those sums in time.
-/

@[expose] public section

open Filter Set Finset
open scoped NNReal Topology

namespace StochLean

noncomputable def quadraticPairSum {S : ℝ≥0} (π : TimePartition S)
    (Φ : ℝ → ℝ → ℝ) (x : ℝ≥0 → ℝ) (t : ℝ≥0) : ℝ :=
  ∑ i : Fin π.size,
    Φ (x (min (π.left i) t)) (x (min (π.right i) t)) *
      (x (min (π.right i) t) - x (min (π.left i) t)) ^ 2

@[simp] theorem quadraticPairSum_zero {S : ℝ≥0} (π : TimePartition S)
    (Φ : ℝ → ℝ → ℝ) (x : ℝ≥0 → ℝ) : quadraticPairSum π Φ x 0 = 0 := by
  simp [quadraticPairSum]

theorem norm_quadraticPairSum_le {S : ℝ≥0} (π : TimePartition S)
    (Φ : ℝ → ℝ → ℝ) (x : ℝ≥0 → ℝ) (t : ℝ≥0) {C : ℝ}
    (hC : ∀ i : Fin π.size,
      ‖Φ (x (min (π.left i) t)) (x (min (π.right i) t))‖ ≤ C) :
    ‖quadraticPairSum π Φ x t‖ ≤ C * quadraticVariationSum π (fun u ↦ x (min u t)) := by
  unfold quadraticPairSum
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑ i : Fin π.size, C * (x (min (π.right i) t) - x (min (π.left i) t)) ^ 2 := by
      apply sum_le_sum
      intro i _
      simp only [norm_mul, norm_pow, Real.norm_eq_abs, sq_abs]
      exact mul_le_mul_of_nonneg_right (hC i) (sq_nonneg _)
    _ = _ := by rw [← mul_sum]; rfl

theorem tendstoUniformlyOn_quadraticPairSum_zero {S : ℕ → ℝ≥0}
    (π : ∀ n, TimePartition (S n)) {T : ℝ≥0} {x : ℝ≥0 → ℝ}
    (hx : ContinuousOn x (Icc 0 T)) {Φ : ℝ → ℝ → ℝ}
    (hΦ : Continuous (fun p : ℝ × ℝ ↦ Φ p.1 p.2)) (hdiag : ∀ a, Φ a a = 0)
    (hmesh : Tendsto (fun n ↦ ((π n).mesh : ℝ)) atTop (𝓝 0))
    {B : ℝ} (hB : 0 ≤ B)
    (hb : ∀ᶠ n in atTop, ∀ t ∈ Icc 0 T,
      quadraticVariationSum (π n) (fun u ↦ x (min u t)) ≤ B) :
    TendstoUniformlyOn (fun n ↦ quadraticPairSum (π n) Φ x) (fun _ ↦ 0) atTop (Icc 0 T) := by
  apply Metric.tendstoUniformlyOn_iff.mpr
  intro ε hε
  have hden : 0 < B + 1 := by linarith
  have he : 0 < ε / (B + 1) := div_pos hε hden
  obtain ⟨δ, hδ, hmod⟩ := exists_pair_diagonal_modulus_of_continuous hx hΦ hdiag he
  filter_upwards [hmesh.eventually_lt_const hδ, hb] with n hn hbound
  intro t ht
  have hcoeff (i : Fin (π n).size) :
      ‖Φ (x (min ((π n).left i) t)) (x (min ((π n).right i) t))‖ ≤ ε / (B + 1) :=
    (hmod _ ⟨bot_le, (min_le_right _ _).trans ht.2⟩
      _ ⟨bot_le, (min_le_right _ _).trans ht.2⟩
      (((π n).dist_stopped_endpoints_le_mesh t i).trans_lt hn)).le
  have hnrm : ‖quadraticPairSum (π n) Φ x t‖ < ε := by
    calc
      _ ≤ ε / (B + 1) * quadraticVariationSum (π n) (fun u ↦ x (min u t)) :=
        norm_quadraticPairSum_le (π n) Φ x t hcoeff
      _ ≤ ε / (B + 1) * B := mul_le_mul_of_nonneg_left (hbound t ht) he.le
      _ < ε / (B + 1) * (B + 1) := mul_lt_mul_of_pos_left (lt_add_one B) he
      _ = ε := div_mul_cancel₀ ε (ne_of_gt hden)
  simpa only [dist_zero_left] using hnrm

end StochLean
