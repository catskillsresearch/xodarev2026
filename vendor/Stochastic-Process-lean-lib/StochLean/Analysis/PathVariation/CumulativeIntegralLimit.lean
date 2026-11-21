/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Analysis.PathVariation.CompletedSums
public import StochLean.Analysis.PathVariation.StieltjesIntegralRiemann
public import StochLean.Analysis.PathVariation.UniformPartition

/-! # Continuous weighted limits of finite nonnegative cumulative sums

Pointwise convergence of cumulative masses identifies the actual path Stieltjes
integral. The proof uses finite step approximation and retains the initial mass;
neither atom locations nor successive finite families need be nested.
-/

@[expose] public section

open Filter Set Finset
open scoped NNReal Topology

namespace StochLean

theorem TimePartition.sum_leftStep_mul_eq_cumulative {T : ℝ≥0} (π : TimePartition T)
    {ι : Type*} [Fintype ι] (a : ι → ℝ≥0) (c : ι → ℝ) (f : ℝ≥0 → ℝ) :
    (∑ i, π.leftStep f (a i) * c i) = f 0 * cumulativeStepSum a c 0 +
      ∑ j : Fin π.size, f (π.left j) *
        (cumulativeStepSum a c (π.right j) - cumulativeStepSum a c (π.left j)) := by
  classical
  have hterm (i : ι) : π.leftStep f (a i) * c i =
      f 0 * (if a i ≤ 0 then c i else 0) +
        ∑ j : Fin π.size, f (π.left j) *
          ((if a i ≤ π.right j then c i else 0) -
            (if a i ≤ π.left j then c i else 0)) := by
    by_cases hi : a i = 0
    · simp [hi]
    · rw [TimePartition.leftStep, if_neg hi]
      simp only [nonpos_iff_eq_zero, hi, ↓reduceIte, mul_zero, zero_add, sum_mul]
      apply sum_congr rfl
      intro j _
      by_cases hl : a i ≤ π.left j
      · simp [hl, hl.trans (π.left_le_right j)]
      · by_cases hr : a i ≤ π.right j
        · simp [indicator_of_mem (show a i ∈ Ioc (π.left j) (π.right j) from
            ⟨lt_of_not_ge hl, hr⟩), hl, hr]
        · simp [hl, hr]
  simp_rw [hterm]
  rw [sum_add_distrib, sum_comm]
  simp only [cumulativeStepSum, mul_sum, ← sum_sub_distrib, mul_sub]

theorem tendsto_weighted_cumulativeStepSum {T : ℝ≥0} {k : ℕ → ℕ}
    (a : ∀ n, Fin (k n) → ℝ≥0) (c : ∀ n, Fin (k n) → ℝ)
    (ha : ∀ n i, a n i ≤ T) (hc : ∀ n i, 0 ≤ c n i)
    {A : ℝ≥0 → ℝ} {hv : LocallyBoundedVariationOn A univ}
    {hr : ∀ t, ContinuousWithinAt A (Ici t) t}
    (hlim : ∀ t ∈ Icc 0 T,
      Tendsto (fun n ↦ cumulativeStepSum (a n) (c n) t) atTop (𝓝 (A t)))
    {f : ℝ≥0 → ℝ} (hf : ContinuousOn f (Icc 0 T)) :
    Tendsto (fun n ↦ ∑ i : Fin (k n), f (a n i) * c n i) atTop
      (𝓝 (pathStieltjesIntegral A hv hr f T)) := by
  let π : ℕ → TimePartition T := fun m ↦ (LocallyFinitePartition.dyadic m).restrict T
  have hm : Tendsto (fun m ↦ ((π m).mesh : ℝ)) atTop (𝓝 0) := by
    exact_mod_cast (NNReal.continuous_coe.tendsto 0).comp
      (LocallyFinitePartition.dyadic_admissible.restrict_mesh_tendsto (fun _ ↦ T))
  have hstep := TimePartition.tendstoUniformlyOn_leftStep hf hm
  have hint := tendsto_stieltjesLeftSum_terminal (x := A) (hx := hv) (hr := hr) hf hm
  have hmass : Tendsto (fun n ↦ ∑ i : Fin (k n), c n i) atTop (𝓝 (A T)) := by
    simpa only [cumulativeStepSum, ha, ↓reduceIte] using hlim T ⟨bot_le, le_rfl⟩
  let B : ℝ := |A T| + 1
  have hB : 0 < B := by dsimp [B]; positivity
  have hb : ∀ᶠ n in atTop, (∑ i : Fin (k n), c n i) ≤ B :=
    (hmass.eventually_lt_const (show A T < B from
      (le_abs_self _).trans_lt (lt_add_one _))).mono fun _ hn ↦ hn.le
  have hcoarse (m : ℕ) :
      Tendsto (fun n ↦ ∑ i : Fin (k n), (π m).leftStep f (a n i) * c n i) atTop
        (𝓝 (f 0 * A 0 + ∑ j : Fin (π m).size, f ((π m).left j) * (π m).increment A j)) := by
    simp_rw [TimePartition.sum_leftStep_mul_eq_cumulative]
    exact ((hlim 0 ⟨le_rfl, bot_le⟩).const_mul (f 0)).add
      (tendsto_finsetSum _ fun j _ ↦
        ((hlim _ ⟨bot_le, (π m).point_le_horizon _⟩).sub
          (hlim _ ⟨bot_le, (π m).point_le_horizon _⟩)).const_mul (f ((π m).left j)))
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  have he : 0 < ε / (3 * B) := div_pos hε (by positivity)
  obtain ⟨m, happrox, htarget⟩ :=
    ((Metric.tendstoUniformlyOn_iff.mp hstep (ε / (3 * B)) he).and
      (Metric.tendsto_nhds.mp hint (ε / 3) (by positivity))).exists
  filter_upwards [hb, Metric.tendsto_nhds.mp (hcoarse m) (ε / 3) (by positivity)] with n hn hcn
  have herr : dist (∑ i : Fin (k n), f (a n i) * c n i)
      (∑ i : Fin (k n), (π m).leftStep f (a n i) * c n i) ≤ ε / 3 := by
    rw [dist_eq_norm, ← sum_sub_distrib]
    calc
      _ ≤ ∑ i : Fin (k n), ‖f (a n i) * c n i - (π m).leftStep f (a n i) * c n i‖ :=
        norm_sum_le _ _
      _ ≤ ∑ i : Fin (k n), ε / (3 * B) * c n i := by
        apply sum_le_sum
        intro i _
        rw [← sub_mul, norm_mul, Real.norm_eq_abs (c n i), abs_of_nonneg (hc n i)]
        exact mul_le_mul_of_nonneg_right
          (by simpa only [dist_eq_norm] using (happrox (a n i) ⟨bot_le, ha n i⟩).le) (hc n i)
      _ = ε / (3 * B) * ∑ i : Fin (k n), c n i := (mul_sum ..).symm
      _ ≤ ε / (3 * B) * B := mul_le_mul_of_nonneg_left hn he.le
      _ = ε / 3 := by field_simp
  have hd₁ := dist_triangle (∑ i : Fin (k n), f (a n i) * c n i)
    (∑ i : Fin (k n), (π m).leftStep f (a n i) * c n i)
    (pathStieltjesIntegral A hv hr f T)
  have hd₂ := dist_triangle (∑ i : Fin (k n), (π m).leftStep f (a n i) * c n i)
    (f 0 * A 0 + ∑ j : Fin (π m).size, f ((π m).left j) * (π m).increment A j)
    (pathStieltjesIntegral A hv hr f T)
  linarith

end StochLean
