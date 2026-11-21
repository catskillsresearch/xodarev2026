/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Martingale.OptionalSampling.OneSidedUpperApprox
public import StochLean.Probability.Martingale.OptionalSampling.ContinuousOneSidedIntegrability
public import StochLean.ForMathlib.MeasureTheory.ConditionalOrder

/-! # Bounded conditional optional sampling for continuous-time one-sided martingales

The actual dyadic upper approximations converge in L1. Finite-partition
conditional inequalities therefore pass to set-integral inequalities on the
earlier stopping sigma-field. Progressive measurability identifies the earlier
value there. No Class D, nonnegativity, global L1 bound or L2 assumption is used.
-/

@[expose] public section

open ProbabilityTheory StochLean Filter
open scoped NNReal ENNReal Topology

namespace MeasureTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsFiniteMeasure P]
  {F : Filtration ℝ≥0 mΩ} {X : ℝ≥0 → Ω → ℝ}

theorem Submartingale.finiteStoppingTime_value_ae_le_condExp_of_le_of_progressive
    (hX : Submartingale X F P) (hprog : IsStronglyProgressive F X)
    (hr : HasRightContinuousPaths X P) (σ τ : FiniteStoppingTime F)
    (hle : ∀ ω, σ ω ≤ τ ω) {T : ℝ≥0} (hb : ∀ ω, τ ω ≤ T) :
    (fun ω ↦ X (σ ω) ω) ≤ᵐ[P] P[(fun ω ↦ X (τ ω) ω) | σ.measurableSpace] := by
  have hs (ω) : σ ω ≤ T := (hle ω).trans (hb ω)
  have hiσ := hX.integrable_finiteStoppingTime_value σ hs hr
  have hiτ := hX.integrable_finiteStoppingTime_value τ hb hr
  apply ae_le_condExp_of_forall_setIntegral_le σ.measurableSpace_le hiσ hiτ
    (measurable_stoppedValue hprog σ.isStoppingTime).stronglyMeasurable
  intro A hA
  have hlimσ := tendsto_setIntegral_of_L1' (fun ω ↦ X (σ ω) ω) hiσ.aestronglyMeasurable
    (Eventually.of_forall fun n ↦ hX.integrable_upperApprox_value σ T (2 ^ n - 1))
    (hX.tendsto_eLpNorm_dyadic_upperApprox_value σ hs hr) A
  have hlimτ := tendsto_setIntegral_of_L1' (fun ω ↦ X (τ ω) ω) hiτ.aestronglyMeasurable
    (Eventually.of_forall fun n ↦ hX.integrable_upperApprox_value τ T (2 ^ n - 1))
    (hX.tendsto_eLpNorm_dyadic_upperApprox_value τ hb hr) A
  apply le_of_tendsto_of_tendsto' hlimσ hlimτ
  intro n
  let σn := σ.upperApprox T (2 ^ n - 1)
  let τn := τ.upperApprox T (2 ^ n - 1)
  have hAn : MeasurableSet[σn.measurableSpace] A :=
    σ.isStoppingTime.measurableSpace_mono σn.isStoppingTime
      (fun ω ↦ WithTop.coe_le_coe.mpr (σ.le_upperApprox hs _ ω)) A hA
  have hcomp := hX.finiteStoppingTime_value_ae_le_condExp_of_partition σn τn
    (TimePartition.rightGridPartition T (2 ^ n - 1))
    (TimePartition.upperApprox_mem_rightGridPartition σ T _)
    (TimePartition.upperApprox_mem_rightGridPartition τ T _)
    (σ.upperApprox_mono τ hle T _)
  calc
    _ ≤ ∫ ω in A, P[(fun ω ↦ X (τn ω) ω) | σn.measurableSpace] ω ∂P :=
      setIntegral_mono_ae (hX.integrable_upperApprox_value σ T _).integrableOn
        integrable_condExp.integrableOn hcomp
    _ = _ := setIntegral_condExp σn.measurableSpace_le
      (hX.integrable_upperApprox_value τ T _) hAn

theorem Supermartingale.condExp_finiteStoppingTime_value_ae_le_of_le_of_progressive
    (hX : Supermartingale X F P) (hprog : IsStronglyProgressive F X)
    (hr : HasRightContinuousPaths X P) (σ τ : FiniteStoppingTime F)
    (hle : ∀ ω, σ ω ≤ τ ω) {T : ℝ≥0} (hb : ∀ ω, τ ω ≤ T) :
    P[(fun ω ↦ X (τ ω) ω) | σ.measurableSpace] ≤ᵐ[P] (fun ω ↦ X (σ ω) ω) := by
  have hneg : HasRightContinuousPaths (-X) P := by
    filter_upwards [hr] with ω hω t
    exact (hω t).neg
  have h := hX.neg.finiteStoppingTime_value_ae_le_condExp_of_le_of_progressive
    hprog.neg hneg σ τ hle hb
  change (fun ω ↦ -X (σ ω) ω) ≤ᵐ[P]
    P[-(fun ω ↦ X (τ ω) ω) | σ.measurableSpace] at h
  filter_upwards [h, condExp_neg (fun ω ↦ X (τ ω) ω) σ.measurableSpace] with ω hω heω
  rw [heω] at hω
  exact neg_le_neg_iff.mp hω

end MeasureTheory
