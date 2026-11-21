/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Martingale.OptionalSampling.PartitionOneSided
public import StochLean.Probability.Martingale.Convergence.ReverseOneSided
public import StochLean.Probability.Process.Stopping.DyadicMonotone
public import StochLean.Probability.Process.Stopping.UpperApproxPartition
public import StochLean.Analysis.PathVariation.CommonRefinement
public import StochLean.ForMathlib.MeasureTheory.Function.UniformIntegrableOperations

/-! # Uniform integrability of decreasing one-sided stopping approximations

The dyadic subsequence of the existing capped upper approximations gives a
reverse supermartingale in its native stopping filtration. Finite-partition
conditional sampling and the previously proved expectation bound establish
this fact. Reverse one-sided UI then gives L1 convergence under right continuity.
This asserts UI of this approximation sequence, not of all bounded stopping values.
-/

@[expose] public section

open ProbabilityTheory StochLean Filter
open scoped NNReal ENNReal Topology

namespace MeasureTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsFiniteMeasure P]
  {F : Filtration ℝ≥0 mΩ} {X : ℝ≥0 → Ω → ℝ}

theorem Supermartingale.uniformIntegrable_dyadic_upperApprox_value
    (hX : Supermartingale X F P) (τ : FiniteStoppingTime F) (T : ℝ≥0) :
    UniformIntegrable (fun n ω ↦ X (τ.upperApprox T (2 ^ n - 1) ω) ω) 1 P := by
  let S (n : ℕᵒᵈ) := τ.upperApprox T (2 ^ OrderDual.ofDual n - 1)
  have hSle {i j : ℕᵒᵈ} (hij : i ≤ j) (ω : Ω) : S i ω ≤ S j ω :=
    (τ.antitone_dyadic_upperApprox T ω) hij
  let G : Filtration ℕᵒᵈ mΩ :=
    ⟨fun n ↦ (S n).measurableSpace,
      fun i j hij ↦ (S i).isStoppingTime.measurableSpace_mono (S j).isStoppingTime
        (fun ω ↦ WithTop.coe_le_coe.mpr (hSle hij ω)), fun n ↦ (S n).measurableSpace_le⟩
  let π (n : ℕᵒᵈ) := TimePartition.rightGridPartition T (2 ^ OrderDual.ofDual n - 1)
  have hmem (n : ℕᵒᵈ) (ω : Ω) : S n ω ∈ Set.range (π n).point :=
    TimePartition.upperApprox_mem_rightGridPartition τ T _ ω
  have hb (n : ℕᵒᵈ) (ω : Ω) : S n ω ≤ T := τ.upperApprox_le_horizon T _ ω
  have hY : Supermartingale (fun n ω ↦ X (S n ω) ω) G P := by
    refine ⟨fun n ↦ hX.stronglyAdapted.stronglyMeasurable_partitionStoppingValue
      (S n) (π n) (hb n) (hmem n), fun i j hij ↦ ?_,
      fun n ↦ hX.integrable_upperApprox_value τ T _⟩
    exact hX.condExp_finiteStoppingTime_value_ae_le_of_partition (S i) (S j)
      ((π i).commonRefinement (π j))
      (fun ω ↦ (π i).commonRefinement_refines_left (π j) (hmem i ω))
      (fun ω ↦ (π i).commonRefinement_refines_right (π j) (hmem j ω)) (hSle hij)
  have hUI := hY.uniformIntegrable_of_reverse_expectation_bounded
    (C := ∫ ω, X 0 ω ∂P) (fun n ↦ hX.integral_upperApprox_value_le_initial τ T _)
  exact hUI.reindex OrderDual.toDual

theorem Submartingale.uniformIntegrable_dyadic_upperApprox_value
    (hX : Submartingale X F P) (τ : FiniteStoppingTime F) (T : ℝ≥0) :
    UniformIntegrable (fun n ω ↦ X (τ.upperApprox T (2 ^ n - 1) ω) ω) 1 P := by
  apply (hX.neg.uniformIntegrable_dyadic_upperApprox_value τ T).mono_norm
    (fun n ↦ (hX.integrable_upperApprox_value τ T _).aestronglyMeasurable)
  intro n
  exact Eventually.of_forall fun ω ↦ (norm_neg (X (τ.upperApprox T (2 ^ n - 1) ω) ω)).ge

omit [IsFiniteMeasure P] in
private theorem ae_tendsto_dyadic_upperApprox_value (τ : FiniteStoppingTime F) {T : ℝ≥0}
    (hb : ∀ ω, τ ω ≤ T) (hr : HasRightContinuousPaths X P) :
    ∀ᵐ ω ∂P, Tendsto (fun n ↦ X (τ.upperApprox T (2 ^ n - 1) ω) ω) atTop
      (nhds (X (τ ω) ω)) := by
  filter_upwards [hr] with ω hω
  exact (hω (τ ω)).tendsto.comp (τ.tendsto_dyadic_upperApprox hb ω)

theorem Supermartingale.tendsto_eLpNorm_dyadic_upperApprox_value
    (hX : Supermartingale X F P) (τ : FiniteStoppingTime F) {T : ℝ≥0}
    (hb : ∀ ω, τ ω ≤ T) (hr : HasRightContinuousPaths X P) :
    Tendsto (fun n ↦ eLpNorm ((fun ω ↦ X (τ.upperApprox T (2 ^ n - 1) ω) ω) -
      (fun ω ↦ X (τ ω) ω)) 1 P) atTop (nhds 0) := by
  have hu := hX.uniformIntegrable_dyadic_upperApprox_value τ T
  have hl := ae_tendsto_dyadic_upperApprox_value τ hb hr
  exact tendsto_Lp_finite_of_tendsto_ae le_rfl ENNReal.one_ne_top hu.1
    (hu.memLp_of_ae_tendsto hl) hu.2.1 hl

theorem Submartingale.tendsto_eLpNorm_dyadic_upperApprox_value
    (hX : Submartingale X F P) (τ : FiniteStoppingTime F) {T : ℝ≥0}
    (hb : ∀ ω, τ ω ≤ T) (hr : HasRightContinuousPaths X P) :
    Tendsto (fun n ↦ eLpNorm ((fun ω ↦ X (τ.upperApprox T (2 ^ n - 1) ω) ω) -
      (fun ω ↦ X (τ ω) ω)) 1 P) atTop (nhds 0) := by
  have hu := hX.uniformIntegrable_dyadic_upperApprox_value τ T
  have hl := ae_tendsto_dyadic_upperApprox_value τ hb hr
  exact tendsto_Lp_finite_of_tendsto_ae le_rfl ENNReal.one_ne_top hu.1
    (hu.memLp_of_ae_tendsto hl) hu.2.1 hl

end MeasureTheory
