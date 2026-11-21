/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Analysis.PathVariation.FiniteVariation
public import StochLean.Internal.Brownian.Gaussian.Moment
public import Mathlib.Probability.BrownianMotion.Basic
public import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Basic
public import Mathlib.MeasureTheory.Function.ConvergenceInMeasure

/-!
# Brownian quadratic increment sums: moments and convergence in probability

These are the quantitative prerequisites of Klenke 21.64. They do not replace
the stronger almost-sure, all-times conclusion for arbitrary nested admissible
partitions; the reverse-martingale proof of that conclusion is a separate task.
-/

@[expose] public section

open MeasureTheory Filter Set Finset StochLean
open scoped NNReal ENNReal Topology ProbabilityTheory

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
  {B : ℝ≥0 → Ω → ℝ} {T : ℝ≥0}

private theorem integral_four_gaussian_zero (v : ℝ≥0) :
    (∫ x : ℝ, x ^ 4 ∂gaussianReal 0 v) = 3 * (v : ℝ) ^ 2 := by
  have h := centralMoment_two_mul_gaussianReal 0 v.sqrt 2
  rw [NNReal.sq_sqrt] at h
  norm_num [centralMoment, Nat.doubleFactorial] at h
  have hs : (Real.sqrt v) ^ 2 = (v : ℝ) := Real.sq_sqrt v.coe_nonneg
  calc
    _ = (Real.sqrt v) ^ 4 * 3 := h
    _ = 3 * (v : ℝ) ^ 2 := by nlinarith [sq_nonneg ((Real.sqrt v) ^ 2 - v)]

set_option backward.isDefEq.respectTransparency.types false in
theorem IsPreBrownianReal.hasLaw_partitionIncrement (hB : IsPreBrownianReal B P)
    (π : TimePartition T) (i : Fin π.size) :
    HasLaw (fun ω ↦ π.increment (B · ω) i) (gaussianReal 0 (π.gap i)) P := by
  have h := hB.hasLaw_sub (π.right i) (π.left i)
  have heq : nndist (π.right i : ℝ) (π.left i : ℝ) = π.gap i := by
    apply NNReal.coe_injective
    change |(π.right i : ℝ) - (π.left i : ℝ)| = (π.gap i : ℝ)
    rw [abs_of_nonneg (sub_nonneg.mpr (by exact_mod_cast π.left_le_right i))]
    exact (NNReal.coe_sub (π.left_le_right i)).symm
  convert h using 1
  · rfl
  · exact congrArg (gaussianReal 0) heq.symm

theorem IsPreBrownianReal.memLp_partitionIncrement_sq (hB : IsPreBrownianReal B P)
    (π : TimePartition T) (i : Fin π.size) :
    MemLp (fun ω ↦ (π.increment (B · ω) i) ^ 2) 2 P := by
  have h4 : MemLp (fun ω ↦ π.increment (B · ω) i) 4 P :=
    (hB.hasLaw_partitionIncrement π i).hasGaussianLaw.memLp (by norm_num)
  let : ENNReal.HolderTriple 4 4 2 := ⟨by
    have h : (4 : ℝ≥0)⁻¹ + 4⁻¹ = 2⁻¹ := by norm_num
    have h' := congrArg (fun x : ℝ≥0 ↦ (x : ℝ≥0∞)) h
    simpa only [ENNReal.coe_add, ENNReal.coe_inv (by norm_num : (4 : ℝ≥0) ≠ 0),
      ENNReal.coe_inv (by norm_num : (2 : ℝ≥0) ≠ 0), ENNReal.coe_ofNat] using h'⟩
  simpa only [pow_two] using h4.mul' h4

theorem IsPreBrownianReal.integral_partitionIncrement_sq (hB : IsPreBrownianReal B P)
    (π : TimePartition T) (i : Fin π.size) :
    (∫ ω, (π.increment (B · ω) i) ^ 2 ∂P) = π.gap i := by
  let : IsProbabilityMeasure P := (hB.hasLaw_eval 0).isProbabilityMeasure
  have hL := hB.hasLaw_partitionIncrement π i
  have h := variance_eq_sub hL.hasGaussianLaw.memLp_two
  rw [hL.variance_eq, variance_id_gaussianReal, hL.integral_eq, integral_id_gaussianReal] at h
  simpa using h.symm

theorem IsPreBrownianReal.integral_partitionIncrement_four (hB : IsPreBrownianReal B P)
    (π : TimePartition T) (i : Fin π.size) :
    (∫ ω, (π.increment (B · ω) i) ^ 4 ∂P) = 3 * (π.gap i : ℝ) ^ 2 := by
  have hL := hB.hasLaw_partitionIncrement π i
  change (∫ ω, ((fun x : ℝ ↦ x ^ 4) ∘ (fun ω ↦ π.increment (B · ω) i)) ω ∂P) = _
  rw [hL.integral_comp (by fun_prop), integral_four_gaussian_zero]

theorem IsPreBrownianReal.variance_partitionIncrement_sq (hB : IsPreBrownianReal B P)
    (π : TimePartition T) (i : Fin π.size) :
    Var[fun ω ↦ (π.increment (B · ω) i) ^ 2; P] = 2 * (π.gap i : ℝ) ^ 2 := by
  let : IsProbabilityMeasure P := (hB.hasLaw_eval 0).isProbabilityMeasure
  rw [variance_eq_sub (hB.memLp_partitionIncrement_sq π i),
    hB.integral_partitionIncrement_sq]
  simp only [Pi.pow_apply, ← pow_mul, show 2 * 2 = 4 from rfl]
  rw [hB.integral_partitionIncrement_four]
  ring

theorem IsPreBrownianReal.memLp_quadraticVariationSum (hB : IsPreBrownianReal B P)
    (π : TimePartition T) : MemLp (fun ω ↦ quadraticVariationSum π (B · ω)) 2 P := by
  have heq : (fun ω ↦ quadraticVariationSum π (B · ω)) =
      ∑ i, (fun ω ↦ (π.increment (B · ω) i) ^ 2) := by
    funext ω
    simp only [quadraticVariationSum, Finset.sum_apply]
  rw [heq]
  exact memLp_finsetSum' Finset.univ (fun i _ ↦ hB.memLp_partitionIncrement_sq π i)

theorem IsPreBrownianReal.integral_quadraticVariationSum (hB : IsPreBrownianReal B P)
    (π : TimePartition T) : (∫ ω, quadraticVariationSum π (B · ω) ∂P) = T := by
  let : IsProbabilityMeasure P := (hB.hasLaw_eval 0).isProbabilityMeasure
  simp only [quadraticVariationSum]
  rw [integral_finsetSum _
    (fun i _ ↦ (hB.memLp_partitionIncrement_sq π i).integrable (by norm_num))]
  simp only [hB.integral_partitionIncrement_sq]
  exact π.sum_gap

theorem IsPreBrownianReal.variance_quadraticVariationSum (hB : IsPreBrownianReal B P)
    (π : TimePartition T) :
    Var[fun ω ↦ quadraticVariationSum π (B · ω); P] = 2 * ∑ i, (π.gap i : ℝ) ^ 2 := by
  have hind := (hB.hasIndepIncrements π.size π.point π.monotone_point).comp
    (fun _ (x : ℝ) ↦ x ^ 2) (fun _ ↦ by fun_prop)
  have hv := IndepFun.variance_sum (s := (Finset.univ : Finset (Fin π.size)))
    (fun i _ ↦ hB.memLp_partitionIncrement_sq π i)
    (fun i _ j _ hij ↦ hind.indepFun hij)
  have heq : (fun ω ↦ quadraticVariationSum π (B · ω)) =
      ∑ i, (fun ω ↦ (π.increment (B · ω) i) ^ 2) := by
    funext ω
    simp only [quadraticVariationSum, Finset.sum_apply]
  rw [heq, hv]
  simp only [hB.variance_partitionIncrement_sq, mul_sum]

theorem IsPreBrownianReal.variance_quadraticVariationSum_le (hB : IsPreBrownianReal B P)
    (π : TimePartition T) :
    Var[fun ω ↦ quadraticVariationSum π (B · ω); P] ≤ 2 * T * π.mesh := by
  rw [hB.variance_quadraticVariationSum]
  calc
    2 * ∑ i, (π.gap i : ℝ) ^ 2 ≤ 2 * ∑ i, (π.gap i : ℝ) * π.mesh := by
      simp only [pow_two]
      gcongr with i
      exact_mod_cast π.gap_le_mesh i
    _ = 2 * T * π.mesh := by rw [← sum_mul, π.sum_gap, mul_assoc]

theorem IsPreBrownianReal.measure_quadraticVariationSum_deviation_le
    (hB : IsPreBrownianReal B P) (π : TimePartition T) {ε : ℝ} (hε : 0 < ε) :
    P {ω | ε ≤ |quadraticVariationSum π (B · ω) - T|} ≤
      ENNReal.ofReal (2 * T * π.mesh / ε ^ 2) := by
  let : IsProbabilityMeasure P := (hB.hasLaw_eval 0).isProbabilityMeasure
  have h := meas_ge_le_variance_div_sq (hB.memLp_quadraticVariationSum π) hε
  rw [hB.integral_quadraticVariationSum] at h
  exact h.trans (ENNReal.ofReal_le_ofReal
    (div_le_div_of_nonneg_right (hB.variance_quadraticVariationSum_le π) (sq_nonneg ε)))

/-- Fixed-horizon probability convergence needs only vanishing mesh, not nesting. -/
theorem IsPreBrownianReal.tendstoInMeasure_quadraticVariationSum
    (hB : IsPreBrownianReal B P) {π : ℕ → TimePartition T}
    (hmesh : Tendsto (fun n ↦ ((π n).mesh : ℝ)) atTop (𝓝 0)) :
    TendstoInMeasure P (fun n ω ↦ quadraticVariationSum (π n) (B · ω)) atTop
      (fun _ ↦ (T : ℝ)) := by
  apply tendstoInMeasure_iff_norm.mpr
  intro ε hε
  simp only [Real.norm_eq_abs]
  have hlim : Tendsto (fun n ↦ ENNReal.ofReal (2 * T * (π n).mesh / ε ^ 2))
      atTop (𝓝 0) := by
    have hr := (hmesh.const_mul (2 * (T : ℝ))).div_const (ε ^ 2)
    simpa only [mul_zero, zero_div, ENNReal.ofReal_zero, Function.comp_def] using
      ENNReal.continuous_ofReal.continuousAt.tendsto.comp hr
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim
    (fun _ ↦ bot_le) (fun n ↦ hB.measure_quadraticVariationSum_deviation_le (π n) hε)

/-- The summable-mesh part of the source proof at a fixed horizon.
The full non-summable nested case is intentionally not asserted by this theorem. -/
theorem IsPreBrownianReal.ae_quadraticVariationAlong_of_summable_mesh
    (hB : IsPreBrownianReal B P) {π : ℕ → TimePartition T}
    (hmesh : Summable (fun n ↦ ((π n).mesh : ℝ))) :
    ∀ᵐ ω ∂P, HasQuadraticVariationAlong π (B · ω) T := by
  let ε : ℕ → ℝ := fun k ↦ 1 / ((k : ℝ) + 1)
  have hε : ∀ k, 0 < ε k := fun k ↦ by dsimp [ε]; positivity
  have hev : ∀ k, ∀ᵐ ω ∂P, ∀ᶠ n in atTop,
      |quadraticVariationSum (π n) (B · ω) - T| < ε k := by
    intro k
    have hsum : (∑' n, P {ω | ε k ≤ |quadraticVariationSum (π n) (B · ω) - T|}) ≠ ∞ := by
      apply ne_top_of_le_ne_top
        ((hmesh.mul_left (2 * (T : ℝ))).div_const (ε k ^ 2)).tsum_ofReal_ne_top
      exact ENNReal.tsum_le_tsum fun n ↦
        hB.measure_quadraticVariationSum_deviation_le (π n) (hε k)
    filter_upwards [ae_eventually_notMem hsum] with ω hω
    filter_upwards [hω] with n hn
    exact lt_of_not_ge hn
  filter_upwards [ae_all_iff.mpr hev] with ω hω
  apply Metric.tendsto_atTop.mpr
  intro δ hδ
  obtain ⟨k, hk⟩ := exists_nat_one_div_lt hδ
  obtain ⟨N, hN⟩ := eventually_atTop.mp (hω k)
  refine ⟨N, fun n hn ↦ ?_⟩
  rw [Real.dist_eq]
  exact (hN n hn).trans hk

end ProbabilityTheory
