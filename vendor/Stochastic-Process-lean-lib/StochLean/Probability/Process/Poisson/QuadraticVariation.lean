/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.Poisson.QuadraticVariationSums
public import StochLean.Probability.Process.Poisson.Martingale
public import StochLean.Probability.Process.Semimartingale.QuadraticVariation.Riemann
public import StochLean.Probability.Process.Semimartingale.QuadraticVariation.Subtraction
public import StochLean.Probability.Process.Semimartingale.QuadraticVariation.ContinuousFiniteVariation
public import StochLean.Probability.Process.Semimartingale.QuadraticCovariation.PureJump
public import StochLean.Analysis.PathVariation.Restriction

/-! # The canonical Poisson and compensated-Poisson brackets

The actual raw square bracket is identified by uniqueness of the square-sum
probability limit. Subtracting the continuous finite-variation drift leaves it
unchanged. All identities hold on one event for all times.
-/

@[expose] public section

open MeasureTheory Filter StochLean
open scoped NNReal Topology

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
  {F : Filtration ℝ≥0 mΩ} {N : ℝ≥0 → Ω → ℕ} {rate : ℝ≥0}

theorem IsPoissonProcess.quadraticVariation_real_eq_of_semimartingale
    (hN : IsPoissonProcess N rate P)
    (hS : IsSemimartingale (fun t ω ↦ (N t ω : ℝ)) F P) (hF : F.IsUsual P) :
    Indistinguishable (hS.quadraticVariation hF) (fun t ω ↦ (N t ω : ℝ)) P := by
  let π : ℕ → StoppingTimePartition F := fun n ↦ StoppingTimePartition.deterministic F
    ((LocallyFinitePartition.dyadic n).restrict n)
  have hπ : StoppingTimePartition.IsTendingToIdentity π P :=
    StoppingTimePartition.isTendingToIdentity_of_klenke
      LocallyFinitePartition.dyadic_admissible tendsto_natCast_atTop_atTop
  apply IsModification.indistinguishable_of_rightContinuous _
    (hS.hasCadlagPaths_quadraticVariation hF).hasRightContinuousPaths
    hN.hasCadlagPaths_real.hasRightContinuousPaths
  intro t
  apply tendstoInMeasure_ae_unique
    ((hS.tendstoUCP_quadraticVariationSumProcess hF hπ).fixedTime t)
  have hm := LocallyFinitePartition.dyadic_admissible.restrict_mesh_tendsto (fun _ ↦ t)
  have hn := hN.tendstoInMeasure_quadraticVariationSum_real
    (NNReal.continuous_coe.tendsto 0 |>.comp hm)
  refine TendstoInMeasure.congr' ?_ (Filter.Eventually.of_forall fun _ ↦ rfl) hn
  filter_upwards [(tendsto_natCast_atTop_atTop : Tendsto (fun n : ℕ ↦ (n : ℝ≥0))
    atTop atTop).eventually (eventually_ge_atTop t)] with n hnt
  filter_upwards [hN.initial] with ω h0
  change quadraticVariationSum ((LocallyFinitePartition.dyadic n).restrict t)
    (fun s ↦ (N s ω : ℝ)) = (N 0 ω : ℝ) ^ 2 +
      quadraticVariationSum ((LocallyFinitePartition.dyadic n).restrict n)
        (fun s ↦ (N (min s t) ω : ℝ))
  rw [h0, Nat.cast_zero, zero_pow (by decide : 2 ≠ 0), zero_add]
  exact (LocallyFinitePartition.dyadic n).quadraticVariationSum_restrict_eq_stop hnt
    (fun s ↦ (N s ω : ℝ))

theorem IsPoissonProcess.quadraticVariation_real_eq
    (hN : IsPoissonProcess N rate P) (hF : F.IsUsual P) (ha : Adapted F N) :
    Indistinguishable ((hN.isSemimartingale_real hF ha).quadraticVariation hF)
      (fun t ω ↦ (N t ω : ℝ)) P :=
  hN.quadraticVariation_real_eq_of_semimartingale (hN.isSemimartingale_real hF ha) hF

theorem IsPoissonProcess.quadraticVariation_compensated_eq
    (hN : IsPoissonProcess N rate P) (hF : F.IsUsual P) (ha : Adapted F N) :
    Indistinguishable ((hN.isSemimartingale_compensated hF ha).quadraticVariation hF)
      (fun t ω ↦ (N t ω : ℝ)) P := by
  let D : ℝ≥0 → Ω → ℝ := fun t _ ↦ (rate : ℝ) * t
  have hc : HasContinuousPaths D P := ae_of_all _ fun _ ↦
    NNReal.continuous_coe.const_mul (rate : ℝ)
  have hv : HasFiniteVariationPaths D P := by
    apply HasMonotonePaths.hasFiniteVariationPaths
    exact ae_of_all _ fun _ _ _ h ↦ mul_le_mul_of_nonneg_left
      (NNReal.coe_le_coe.mpr h) rate.2
  have hd : IsSemimartingale D F P := hv.isSemimartingale (fun _ ↦ measurable_const)
    hF hc.hasCadlagPaths
  let hS := hN.isSemimartingale_real hF ha
  filter_upwards [hS.quadraticVariation_sub hd hF, hN.quadraticVariation_real_eq hF ha,
    hS.quadraticCovariation_initial_of_continuous_finiteVariation_right hd hF hc hv,
    hd.quadraticVariation_of_continuous_finiteVariation hF hc hv]
    with ω he hq hm hdt t
  change (hS.sub hd).quadraticVariation hF t ω = (N t ω : ℝ)
  rw [he t, hq t, hm t, hdt t]
  simp only [D, NNReal.coe_zero, mul_zero, zero_pow (by decide : 2 ≠ 0), sub_zero,
    add_zero]

end ProbabilityTheory
