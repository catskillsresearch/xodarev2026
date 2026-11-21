/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.Stopping.PartitionIndex
public import StochLean.Probability.Process.Stopping.Approximation
public import StochLean.Analysis.PathVariation.UniformPartition
public import StochLean.Probability.Martingale.OptionalSampling.CountableRangeOneSided
public import Mathlib.MeasureTheory.Function.ConditionalExpectation.Real

/-! # Finite-partition control of the existing upper stopping approximations

Each capped upper approximation lies on a restriction of the existing uniform
partition. Native discrete stopping proves integrability and expectation bounds.
For supermartingales, terminal conditional expectations control the negative
tail, while the initial expectation controls the mean, giving a uniform L1 bound.
This is not yet the continuous-time optional-sampling limit argument.
-/

@[expose] public section

open ProbabilityTheory StochLean MeasureTheory Filter Set
open scoped NNReal ENNReal

namespace StochLean.TimePartition

/-- The existing uniform grid underlying `rightGrid n`, clipped at `T`. -/
noncomputable def rightGridPartition (T : ℝ≥0) (n : ℕ) : TimePartition T :=
  (LocallyFinitePartition.uniform (1 / (n + 1 : ℕ)) (by positivity)).restrict T

theorem upperApprox_mem_rightGridPartition
    {Ω : Type*} {mΩ : MeasurableSpace Ω} {F : Filtration ℝ≥0 mΩ}
    (τ : FiniteStoppingTime F) (T : ℝ≥0) (n : ℕ) (ω : Ω) :
    τ.upperApprox T n ω ∈ Set.range (rightGridPartition T n).point := by
  change min (rightGrid n (τ ω)) T ∈
    Set.range ((LocallyFinitePartition.uniform (1 / (n + 1 : ℕ)) (by positivity)).restrict T).point
  rw [LocallyFinitePartition.mem_range_restrict]
  by_cases h : rightGrid n (τ ω) ≤ T
  · rw [min_eq_left h]
    refine Or.inr ⟨?_, h⟩
    refine ⟨Nat.ceil (((n + 1 : ℕ) : ℝ≥0) * τ ω), ?_⟩
    simp only [rightGrid, div_eq_mul_inv, one_mul]
  · exact Or.inl (min_eq_right (le_of_not_ge h))

end StochLean.TimePartition

namespace MeasureTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsFiniteMeasure P]
  {F : Filtration ℝ≥0 mΩ} {X : ℝ≥0 → Ω → ℝ}

omit [IsFiniteMeasure P] in
theorem Submartingale.integrable_upperApprox_value (hX : Submartingale X F P)
    (τ : FiniteStoppingTime F) (T : ℝ≥0) (n : ℕ) :
    Integrable (fun ω ↦ X (τ.upperApprox T n ω) ω) P :=
  hX.integrable_finiteStoppingTime_value_of_partition (τ.upperApprox T n)
    (TimePartition.rightGridPartition T n) (TimePartition.upperApprox_mem_rightGridPartition τ T n)

theorem Submartingale.integral_initial_le_upperApprox_value (hX : Submartingale X F P)
    (τ : FiniteStoppingTime F) (T : ℝ≥0) (n : ℕ) :
    (∫ ω, X 0 ω ∂P) ≤ ∫ ω, X (τ.upperApprox T n ω) ω ∂P := by
  let π := TimePartition.rightGridPartition T n
  exact hX.expected_finiteStoppingTime_mono_of_partition (FiniteStoppingTime.const F 0)
    (τ.upperApprox T n) π (fun _ ↦ ⟨0, π.first_eq_zero⟩)
    (TimePartition.upperApprox_mem_rightGridPartition τ T n) (fun _ ↦ bot_le)

omit [IsFiniteMeasure P] in
theorem Supermartingale.integrable_upperApprox_value (hX : Supermartingale X F P)
    (τ : FiniteStoppingTime F) (T : ℝ≥0) (n : ℕ) :
    Integrable (fun ω ↦ X (τ.upperApprox T n ω) ω) P := by
  have h : Integrable (-(fun ω ↦ X (τ.upperApprox T n ω) ω)) P :=
    hX.neg.integrable_upperApprox_value τ T n
  exact integrable_neg_iff.mp h

theorem Supermartingale.integral_upperApprox_value_le_initial (hX : Supermartingale X F P)
    (τ : FiniteStoppingTime F) (T : ℝ≥0) (n : ℕ) :
    (∫ ω, X (τ.upperApprox T n ω) ω ∂P) ≤ ∫ ω, X 0 ω ∂P := by
  simpa only [Pi.neg_apply, integral_neg, neg_le_neg_iff] using
    hX.neg.integral_initial_le_upperApprox_value τ T n

theorem Supermartingale.condExp_le_upperApprox_value (hX : Supermartingale X F P)
    (τ : FiniteStoppingTime F) (T : ℝ≥0) (n : ℕ) :
    P[X T | (τ.upperApprox T n).measurableSpace] ≤ᵐ[P]
      (fun ω ↦ X (τ.upperApprox T n ω) ω) := by
  have hc : (Set.range (τ.upperApprox T n).withTop).Countable := by
    apply ((τ.countable_range_upperApprox T n).image
      (fun t : ℝ≥0 ↦ (t : WithTop ℝ≥0))).mono
    rintro t ⟨ω, rfl⟩
    exact ⟨τ.upperApprox T n ω, ⟨ω, rfl⟩, rfl⟩
  exact hX.condExp_ae_le_stoppedValue_of_le_const_of_countable_range
    (τ.upperApprox T n).isStoppingTime
    (fun ω ↦ WithTop.coe_le_coe.mpr (τ.upperApprox_le_horizon T n ω)) hc

theorem Supermartingale.integral_norm_upperApprox_value_le (hX : Supermartingale X F P)
    (τ : FiniteStoppingTime F) (T : ℝ≥0) (n : ℕ) :
    (∫ ω, ‖X (τ.upperApprox T n ω) ω‖ ∂P) ≤
      (∫ ω, X 0 ω ∂P) + 2 * (∫ ω, ‖X T ω‖ ∂P) := by
  have hi := hX.integrable_upperApprox_value τ T n
  have hc : Integrable P[X T | (τ.upperApprox T n).measurableSpace] P := integrable_condExp
  calc
    _ ≤ ∫ ω, X (τ.upperApprox T n ω) ω +
        2 * ‖P[X T | (τ.upperApprox T n).measurableSpace] ω‖ ∂P := by
      apply integral_mono_ae hi.norm (hi.add (hc.norm.const_mul 2))
      filter_upwards [hX.condExp_le_upperApprox_value τ T n] with ω hω
      change ‖X (τ.upperApprox T n ω) ω‖ ≤ X (τ.upperApprox T n ω) ω +
        2 * ‖P[X T | (τ.upperApprox T n).measurableSpace] ω‖
      simp only [Real.norm_eq_abs]
      rw [abs_le]
      constructor
      · linarith [neg_le_abs (P[X T | (τ.upperApprox T n).measurableSpace] ω)]
      · linarith [abs_nonneg (P[X T | (τ.upperApprox T n).measurableSpace] ω)]
    _ = (∫ ω, X (τ.upperApprox T n ω) ω ∂P) +
        2 * (∫ ω, ‖P[X T | (τ.upperApprox T n).measurableSpace] ω‖ ∂P) := by
      rw [integral_add hi (hc.norm.const_mul 2), integral_const_mul]
    _ ≤ _ := add_le_add (hX.integral_upperApprox_value_le_initial τ T n)
      (mul_le_mul_of_nonneg_left (integral_norm_condExp_le (X T)) (by norm_num))

end MeasureTheory
