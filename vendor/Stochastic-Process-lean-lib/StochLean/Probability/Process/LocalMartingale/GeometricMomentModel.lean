/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import Mathlib.Probability.Distributions.Geometric
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Ring

/-! # A geometric integrable but not square-integrable random variable

Under the existing geometric measure with success probability `3/4`, the
random variable `Z(n) = 2^n` is integrable with mean `3/2`. Its squared values
have infinite lower integral: every term in their weighted series is `3/4`.
Every singleton has positive probability.

This supplies a concrete moment model for Protter's printed-page-128 first
example. No filtration or claim about local square integrability is made here.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology

namespace StochLean.GeometricMomentModel

/-- The fixed parameter of the existing geometric distribution. -/
noncomputable def successProbability : unitInterval :=
  ⟨3 / 4, by constructor <;> norm_num⟩

/-- The canonical geometric measure, specialized to success probability `3/4`. -/
noncomputable def sampleMeasure : Measure ℕ := geometricMeasure successProbability

instance instIsProbabilityMeasureSampleMeasure : IsProbabilityMeasure sampleMeasure := by
  unfold sampleMeasure
  infer_instance

/-- The random variable with a finite first moment and infinite second moment. -/
def value (n : ℕ) : ℝ := 2 ^ n

private theorem successProbability_ne_zero : successProbability ≠ 0 := by
  intro h
  have he := congrArg Subtype.val h
  norm_num [successProbability] at he

theorem sampleMeasure_singleton (n : ℕ) :
    sampleMeasure {n} = ENNReal.ofReal ((1 / 4 : ℝ) ^ n * (3 / 4)) := by
  rw [sampleMeasure, geometricMeasure_singleton successProbability_ne_zero]
  norm_num [successProbability]

theorem sampleMeasure_singleton_pos (n : ℕ) : 0 < sampleMeasure {n} := by
  rw [sampleMeasure_singleton, ENNReal.ofReal_pos]
  exact mul_pos (pow_pos (by norm_num) n) (by norm_num)

private theorem weighted_value (n : ℕ) :
    (1 - (successProbability : ℝ)) ^ n * successProbability * value n =
      (3 / 4 : ℝ) * (1 / 2) ^ n := by
  change (1 - (3 / 4 : ℝ)) ^ n * (3 / 4) * 2 ^ n = _
  rw [show (1 - (3 / 4 : ℝ)) = 1 / 4 by norm_num]
  calc
    (1 / 4 : ℝ) ^ n * (3 / 4) * 2 ^ n =
        (3 / 4) * (((1 / 4 : ℝ) * 2) ^ n) := by rw [mul_pow]; ring
    _ = (3 / 4 : ℝ) * (1 / 2) ^ n := by norm_num

private theorem weighted_square (n : ℕ) :
    (1 - (successProbability : ℝ)) ^ n * successProbability * ‖value n ^ 2‖ =
      (3 / 4 : ℝ) := by
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  change (1 - (3 / 4 : ℝ)) ^ n * (3 / 4) * (2 ^ n) ^ 2 = _
  rw [show (1 - (3 / 4 : ℝ)) = 1 / 4 by norm_num,
    show ((2 : ℝ) ^ n) ^ 2 = ((2 : ℝ) ^ 2) ^ n by
      rw [← pow_mul, ← pow_mul, Nat.mul_comm]]
  calc
    (1 / 4 : ℝ) ^ n * (3 / 4) * (2 ^ 2) ^ n =
        (3 / 4) * (((1 / 4 : ℝ) * 2 ^ 2) ^ n) := by rw [mul_pow]; ring
    _ = (3 / 4 : ℝ) := by norm_num

theorem integrable_value : Integrable value sampleMeasure := by
  apply (integrable_geometricMeasure_iff successProbability_ne_zero).mpr
  refine (hasSum_geometric_two.mul_left (3 / 4 : ℝ)).summable.congr fun n ↦ ?_
  have hn : 0 ≤ value n := pow_nonneg (by norm_num) n
  rw [Real.norm_eq_abs, abs_of_nonneg hn]
  exact (weighted_value n).symm

theorem integral_value : ∫ n, value n ∂sampleMeasure = (3 / 2 : ℝ) := by
  have hi := hasSum_integral_geometricMeasure successProbability_ne_zero integrable_value
  have hg : HasSum (fun n : ℕ ↦ (3 / 4 : ℝ) * (1 / 2) ^ n) (3 / 2 : ℝ) := by
    convert! hasSum_geometric_two.mul_left (3 / 4 : ℝ) using 1
    norm_num
  have hi' : HasSum (fun n : ℕ ↦ (3 / 4 : ℝ) * (1 / 2) ^ n)
      (∫ n, value n ∂sampleMeasure) := by
    simpa only [smul_eq_mul, weighted_value] using! hi
  exact hi'.unique hg

theorem not_integrable_square : ¬ Integrable (fun n ↦ value n ^ 2) sampleMeasure := by
  intro h
  have hs := (integrable_geometricMeasure_iff successProbability_ne_zero).mp h
  have hc : Summable (fun _ : ℕ ↦ (3 / 4 : ℝ)) :=
    hs.congr fun n ↦ weighted_square n
  have hz : (3 / 4 : ℝ) = 0 :=
    tendsto_nhds_unique tendsto_const_nhds hc.tendsto_atTop_zero
  norm_num at hz

/-- The second moment really diverges; no totalized real integral is used. -/
theorem lintegral_square_eq_top :
    ∫⁻ n, ENNReal.ofReal (value n ^ 2) ∂sampleMeasure = ∞ := by
  by_contra h
  apply not_integrable_square
  have hm : StronglyMeasurable (fun n : ℕ ↦ value n ^ 2) := .of_discrete
  refine ⟨hm.aestronglyMeasurable, ?_⟩
  exact (hasFiniteIntegral_iff_ofReal (ae_of_all _ fun n ↦ sq_nonneg (value n))).mpr
    (lt_top_iff_ne_top.mpr h)

theorem not_memLp_two : ¬ MemLp value 2 sampleMeasure := by
  intro h
  exact not_integrable_square ((memLp_two_iff_integrable_sq h.aestronglyMeasurable).mp h)

end StochLean.GeometricMomentModel
