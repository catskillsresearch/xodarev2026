/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.Poisson.SecondMoments
public import StochLean.Analysis.PathVariation.Basic
public import Mathlib.MeasureTheory.Function.ConvergenceInMeasure

/-! # Poisson square-increment sums converge to the actual count

For every finite partition, the square sum exceeds the count and its mean
excess is exactly `rate^2 * sum gap^2`. Thus arbitrary vanishing meshes give
L1 and probability convergence, without assuming unit jumps or a bracket.
-/

@[expose] public section

open MeasureTheory Filter Finset StochLean
open scoped NNReal ENNReal Topology

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
  {N : ℝ≥0 → Ω → ℕ} {rate T : ℝ≥0}

theorem IsPoissonProcess.integrable_quadraticVariationSum_real
    (hN : IsPoissonProcess N rate P) (π : TimePartition T) :
    Integrable (fun ω ↦ quadraticVariationSum π (fun s ↦ (N s ω : ℝ))) P := by
  exact integrable_finsetSum Finset.univ fun i _ ↦
    hN.integrable_real_increment_sq (π.left_le_right i)

theorem IsPoissonProcess.integral_quadraticVariationSum_real_error
    (hN : IsPoissonProcess N rate P) (π : TimePartition T) :
    (∫ ω, (quadraticVariationSum π (fun s ↦ (N s ω : ℝ)) - N T ω) ∂P) =
      (rate : ℝ) ^ 2 * ∑ i, (π.gap i : ℝ) ^ 2 := by
  rw [integral_sub (hN.integrable_quadraticVariationSum_real π) (hN.integrable_real T),
    hN.integral_real]
  simp only [quadraticVariationSum]
  have hint (i : Fin π.size) :
      Integrable (fun ω ↦ (π.increment (fun s ↦ (N s ω : ℝ)) i) ^ 2) P :=
    hN.integrable_real_increment_sq (π.left_le_right i)
  rw [integral_finsetSum _ (fun i _ ↦ hint i)]
  have he (i : Fin π.size) : (∫ ω, (π.increment (fun s ↦ (N s ω : ℝ)) i) ^ 2 ∂P) =
      (rate : ℝ) ^ 2 * (π.gap i : ℝ) ^ 2 + (rate : ℝ) * π.gap i := by
    simp only [TimePartition.increment]
    rw [hN.integral_real_increment_sq (π.left_le_right i)]
    simp only [TimePartition.gap, NNReal.coe_sub (π.left_le_right i)]
    ring
  simp_rw [he]
  rw [sum_add_distrib, ← mul_sum, ← mul_sum, π.sum_gap]
  ring

theorem IsPoissonProcess.quadraticVariationSum_real_ge
    (hN : IsPoissonProcess N rate P) (π : TimePartition T) :
    ∀ᵐ ω ∂P, (N T ω : ℝ) ≤ quadraticVariationSum π (fun s ↦ (N s ω : ℝ)) := by
  filter_upwards [hN.monotonePaths, hN.initial] with ω hm h0
  have he : (N T ω : ℝ) = ∑ i, π.increment (fun s ↦ (N s ω : ℝ)) i := by
    rw [π.sum_increment, h0, Nat.cast_zero, sub_zero]
  rw [he]
  apply sum_le_sum
  intro i _
  have hn := hm (π.left_le_right i)
  change (N (π.right i) ω : ℝ) - N (π.left i) ω ≤
    ((N (π.right i) ω : ℝ) - N (π.left i) ω) ^ 2
  rw [← Nat.cast_sub hn]
  set k := N (π.right i) ω - N (π.left i) ω
  by_cases hk : k = 0
  · simp [hk]
  · have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hk
    nlinarith

theorem IsPoissonProcess.integral_abs_quadraticVariationSum_real_error_le
    (hN : IsPoissonProcess N rate P) (π : TimePartition T) :
    (∫ ω, |quadraticVariationSum π (fun s ↦ (N s ω : ℝ)) - N T ω| ∂P) ≤
      (rate : ℝ) ^ 2 * T * π.mesh := by
  have he : (∫ ω, |quadraticVariationSum π (fun s ↦ (N s ω : ℝ)) - N T ω| ∂P) =
      (∫ ω, (quadraticVariationSum π (fun s ↦ (N s ω : ℝ)) - N T ω) ∂P) := by
    apply integral_congr_ae
    filter_upwards [hN.quadraticVariationSum_real_ge π] with ω hω
    exact abs_of_nonneg (sub_nonneg.mpr hω)
  rw [he, hN.integral_quadraticVariationSum_real_error]
  calc
    (rate : ℝ) ^ 2 * ∑ i, (π.gap i : ℝ) ^ 2 ≤
        (rate : ℝ) ^ 2 * ∑ i, (π.gap i : ℝ) * π.mesh := by
      simp only [pow_two]
      gcongr with i
      exact_mod_cast π.gap_le_mesh i
    _ = (rate : ℝ) ^ 2 * T * π.mesh := by rw [← sum_mul, π.sum_gap, mul_assoc]

theorem IsPoissonProcess.tendstoInMeasure_quadraticVariationSum_real
    (hN : IsPoissonProcess N rate P) {π : ℕ → TimePartition T}
    (hmesh : Tendsto (fun n ↦ ((π n).mesh : ℝ)) atTop (𝓝 0)) :
    TendstoInMeasure P (fun n ω ↦ quadraticVariationSum (π n) (fun s ↦ (N s ω : ℝ)))
      atTop (fun ω ↦ (N T ω : ℝ)) := by
  apply tendstoInMeasure_of_tendsto_eLpNorm (p := 1) (by norm_num)
    (fun n ↦ (hN.integrable_quadraticVariationSum_real (π n)).aestronglyMeasurable)
    (hN.integrable_real T).aestronglyMeasurable
  have hi (n : ℕ) := (hN.integrable_quadraticVariationSum_real (π n)).sub (hN.integrable_real T)
  have hr : Tendsto
      (fun n ↦ ∫ ω, |quadraticVariationSum (π n) (fun s ↦ (N s ω : ℝ)) - N T ω| ∂P)
      atTop (𝓝 0) := by
    apply squeeze_zero (fun _ ↦ integral_nonneg fun _ ↦ abs_nonneg _)
      (fun n ↦ hN.integral_abs_quadraticVariationSum_real_error_le (π n))
    simpa only [mul_zero] using hmesh.const_mul ((rate : ℝ) ^ 2 * T)
  simp_rw [eLpNorm_one_eq_lintegral_enorm, ← ofReal_integral_norm_eq_lintegral_enorm (hi _)]
  simp only [Pi.sub_apply, Real.norm_eq_abs]
  simpa only [Function.comp_def, ENNReal.ofReal_zero] using
    ENNReal.continuous_ofReal.continuousAt.tendsto.comp hr

end ProbabilityTheory
