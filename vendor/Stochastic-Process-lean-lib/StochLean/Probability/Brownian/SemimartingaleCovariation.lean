/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Brownian.QuadraticVariationMoments
public import StochLean.Probability.Brownian.IndependentCombination
public import StochLean.Probability.Process.Semimartingale.QuadraticCovariation.Riemann
public import StochLean.Probability.Process.Semimartingale.QuadraticCovariation.ContinuousLeft
public import StochLean.Probability.Process.Semimartingale.QuadraticVariation.Algebra
public import StochLean.Analysis.PathVariation.Restriction

/-! # Independent Brownian paths and the canonical semimartingale covariation

The existing Brownian square-sum probability limit is compared with the
canonical raw bracket's proved random-partition limit. Exact finite-restriction
transport handles the increasing dyadic horizons. Normalized independent sums
then identify the mixed bracket. No second bracket is defined.
-/

@[expose] public section

open MeasureTheory Filter StochLean
open scoped NNReal Topology

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
  {F : Filtration ℝ≥0 mΩ} {X Y : ℝ≥0 → Ω → ℝ}

theorem IsBrownianReal.quadraticVariation_eq_time_of_semimartingale
    (hX : IsBrownianReal X P) (hSX : IsSemimartingale X F P) (hF : F.IsUsual P) :
    Indistinguishable (hSX.quadraticVariation hF) (fun t _ ↦ (t : ℝ)) P := by
  let π : ℕ → StoppingTimePartition F := fun n ↦ StoppingTimePartition.deterministic F
    ((LocallyFinitePartition.dyadic n).restrict n)
  have hπ : StoppingTimePartition.IsTendingToIdentity π P :=
    StoppingTimePartition.isTendingToIdentity_of_klenke
      LocallyFinitePartition.dyadic_admissible tendsto_natCast_atTop_atTop
  apply IsModification.indistinguishable_of_rightContinuous _
    (hSX.hasCadlagPaths_quadraticVariation hF).hasRightContinuousPaths
    (Filter.Eventually.of_forall fun _ _ ↦ NNReal.continuous_coe.continuousWithinAt)
  intro t
  apply tendstoInMeasure_ae_unique
    ((hSX.tendstoUCP_quadraticVariationSumProcess hF hπ).fixedTime t)
  have hm := LocallyFinitePartition.dyadic_admissible.restrict_mesh_tendsto (fun _ ↦ t)
  have hb := hX.toIsPreBrownianReal.tendstoInMeasure_quadraticVariationSum
    (NNReal.continuous_coe.tendsto 0 |>.comp hm)
  refine TendstoInMeasure.congr' ?_ (Filter.Eventually.of_forall fun _ ↦ rfl) hb
  filter_upwards [(tendsto_natCast_atTop_atTop : Tendsto (fun n : ℕ ↦ (n : ℝ≥0))
    atTop atTop).eventually (eventually_ge_atTop t)] with n hn
  filter_upwards [hX.eval_zero_ae_eq_zero] with ω h0
  change quadraticVariationSum ((LocallyFinitePartition.dyadic n).restrict t) (X · ω) =
    X 0 ω ^ 2 + quadraticVariationSum ((LocallyFinitePartition.dyadic n).restrict n)
      (fun s ↦ X (min s t) ω)
  rw [h0, zero_pow (by decide : 2 ≠ 0), zero_add]
  exact (LocallyFinitePartition.dyadic n).quadraticVariationSum_restrict_eq_stop hn (X · ω)

theorem IsBrownianReal.quadraticCovariation_eq_zero_of_indep
    (hX : IsBrownianReal X P) (hY : IsBrownianReal Y P)
    (hi : IndepFun (fun ω t ↦ X t ω) (fun ω t ↦ Y t ω) P)
    (hSX : IsSemimartingale X F P) (hSY : IsSemimartingale Y F P) (hF : F.IsUsual P) :
    Indistinguishable (hSX.quadraticCovariation hSY hF) 0 P := by
  have hc : 2 * ((Real.sqrt 2)⁻¹) ^ 2 = 1 := by
    rw [inv_pow, Real.sq_sqrt (by norm_num)]
    norm_num
  have hb := hX.add_normalized_of_indep hY hi hc
  let hS := (hSX.add hSY).const_mul ((Real.sqrt 2)⁻¹)
  filter_upwards [hb.quadraticVariation_eq_time_of_semimartingale hS hF,
    hX.quadraticVariation_eq_time_of_semimartingale hSX hF,
    hY.quadraticVariation_eq_time_of_semimartingale hSY hF,
    (hSX.add hSY).quadraticVariation_const_mul hF ((Real.sqrt 2)⁻¹),
    hSX.quadraticVariation_add hSY hF] with ω hs hx hy hm ha t
  have h := hm t
  rw [hs t] at h
  simp only [Pi.smul_apply, smul_eq_mul, ha t, Pi.add_apply, hx t, hy t] at h
  change hSX.quadraticCovariation hSY hF t ω = 0
  nlinarith

theorem IsBrownianReal.continuousQuadraticCovariation_eq_zero_of_indep
    (hX : IsBrownianReal X P) (hY : IsBrownianReal Y P)
    (hi : IndepFun (fun ω t ↦ X t ω) (fun ω t ↦ Y t ω) P)
    (hSX : IsSemimartingale X F P) (hSY : IsSemimartingale Y F P) (hF : F.IsUsual P) :
    Indistinguishable (hSX.continuousQuadraticCovariation hSY hF) 0 P := by
  filter_upwards [hX.quadraticCovariation_eq_zero_of_indep hY hi hSX hSY hF,
    hSX.continuousQuadraticCovariation_eq_of_left_continuous hSY hF hX.cont,
    hX.eval_zero_ae_eq_zero] with ω hq hc h0 t
  rw [hc t, hq t, h0]
  simp only [Pi.zero_apply, zero_mul, sub_zero]

end ProbabilityTheory
