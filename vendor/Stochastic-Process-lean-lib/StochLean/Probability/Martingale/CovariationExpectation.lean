/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Martingale.FiniteCovariation
public import StochLean.Probability.Process.FiniteVariation.Natural
public import StochLean.Probability.Process.Semimartingale.QuadraticCovariation.Riemann
public import StochLean.Analysis.PathVariation.CovariationVariationBound
public import StochLean.Analysis.PathVariation.Stopping
public import Mathlib.MeasureTheory.Function.UniformIntegrable

/-! # Actual mixed-bracket expectation with an integrable-variation martingale

Finite raw mixed sums have terminal-product expectation. Their actual total
variation bound supplies a common L1 dominator, so the existing UCP bracket
limit converges in L1 at each time. No L2 assumption on the FV martingale,
martingale property of its bracket, or Yoeurp lemma is an input.
-/

@[expose] public section

open ProbabilityTheory StochLean Filter Set
open scoped NNReal ENNReal Topology

namespace MeasureTheory.Martingale

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsFiniteMeasure P]
  {F : Filtration ℝ≥0 mΩ} {M A : ℝ≥0 → Ω → ℝ}

/-- The actual raw bracket has terminal-product mean. Integrability follows
from variation domination of the actual approximating mixed sums. -/
theorem integrable_quadraticCovariation_and_integral_eq_of_integrableVariation
    (hM : Martingale M F P) (hA : Martingale A F P) (hF : F.IsUsual P)
    (hcM : HasCadlagPaths M P) (hcA : HasCadlagPaths A P)
    (hv : HasIntegrableVariation A P) (C : ℝ) (hC : 0 ≤ C)
    (hb : ∀ᵐ ω ∂P, ∀ t, ‖M t ω‖ ≤ C) (T : ℝ≥0) :
    let hSM := hM.isSemimartingale_of_bound hF hcM C hb
    let hSA := hv.hasFiniteVariationPaths.isSemimartingale hA.stronglyAdapted.adapted hF hcA
    Integrable (hSM.quadraticCovariation hSA hF T) P ∧
      (∫ ω, hSM.quadraticCovariation hSA hF T ω ∂P) = ∫ ω, M T ω * A T ω ∂P := by
  intro hSM hSA
  let S (n : ℕ) : ℝ≥0 := max n T
  let π (n : ℕ) : TimePartition (S n) := (LocallyFinitePartition.dyadic n).restrict (S n)
  let ρ (n : ℕ) : TimePartition T := (π n).stop T (le_max_right _ _)
  let U (n : ℕ) (ω : Ω) := M 0 ω * A 0 ω + covariationSum (ρ n) (M · ω) (A · ω)
  have hiU (n : ℕ) : Integrable (U n) P :=
    (hM.integrable_raw_covariationSum_and_integral_eq hA hb (ρ n)).1
  have heU (n : ℕ) : (∫ ω, U n ω ∂P) = ∫ ω, M T ω * A T ω ∂P :=
    (hM.integrable_raw_covariationSum_and_integral_eq hA hb (ρ n)).2
  have hS : Tendsto S atTop atTop :=
    tendsto_atTop_mono (fun n ↦ le_max_left (n : ℝ≥0) T) tendsto_natCast_atTop_atTop
  have hπ : StoppingTimePartition.IsTendingToIdentity
      (fun n ↦ StoppingTimePartition.deterministic F (π n)) P :=
    StoppingTimePartition.isTendingToIdentity_of_klenke
      LocallyFinitePartition.dyadic_admissible hS
  have he (n : ℕ) :
      (StoppingTimePartition.deterministic F (π n)).quadraticCovariationSumProcess M A T =
        U n := by
    funext ω
    rfl
  have hprob : TendstoInMeasure P U atTop (hSM.quadraticCovariation hSA hF T) := by
    have hh := (hSM.tendstoUCP_quadraticCovariationSumProcess hSA hF hπ).fixedTime T
    simpa only [he] using hh
  let V (ω : Ω) := ‖M 0 ω * A 0 ω‖ + 2 * C * (eVariationOn (A · ω) univ).toReal
  have hi0 : Integrable (fun ω ↦ M 0 ω * A 0 ω) P := by
    apply ((hA.integrable 0).norm.const_mul C).mono'
      ((hM.integrable 0).aestronglyMeasurable.mul (hA.integrable 0).aestronglyMeasurable)
    filter_upwards [hb] with ω hω
    change ‖M 0 ω * A 0 ω‖ ≤ C * ‖A 0 ω‖
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_right (hω 0) (norm_nonneg _)
  have hiV : Integrable V P :=
    hi0.norm.add (hv.integrable_eVariationOn_toReal.const_mul (2 * C))
  have hdom (n : ℕ) : ∀ᵐ ω ∂P, ‖U n ω‖ ≤ ‖V ω‖ := by
    filter_upwards [hb, hv.ae_eVariationOn_ne_top] with ω hbω hvω
    have hbv : BoundedVariationOn (A · ω) (Icc 0 T) :=
      (show BoundedVariationOn (A · ω) univ from hvω).mono (subset_univ _)
    have hbound := norm_initial_add_covariationSum_le_of_bounded_left (ρ n) hbv
      (fun t _ ↦ hbω t)
    have hvar : (eVariationOn (A · ω) (Icc 0 T)).toReal ≤
        (eVariationOn (A · ω) univ).toReal :=
      ENNReal.toReal_mono hvω (eVariationOn.mono (A · ω) (subset_univ _))
    have hV : 0 ≤ V ω := add_nonneg (norm_nonneg _) (by positivity)
    rw [Real.norm_of_nonneg hV]
    exact hbound.trans (add_le_add le_rfl
      (mul_le_mul_of_nonneg_left hvar (show 0 ≤ 2 * C by positivity)))
  have hui : UniformIntegrable U 1 P :=
    (uniformIntegrable_const le_rfl ENNReal.one_ne_top
      (memLp_one_iff_integrable.mpr hiV)).mono_norm
        (fun n ↦ (hiU n).aestronglyMeasurable) hdom
  have hiQ := hui.integrable_of_tendstoInMeasure hprob
  have hL1 : Tendsto (fun n ↦ eLpNorm (U n - hSM.quadraticCovariation hSA hF T) 1 P)
      atTop (𝓝 0) :=
    tendsto_Lp_finite_of_tendstoInMeasure le_rfl ENNReal.one_ne_top hui.1
      (memLp_one_iff_integrable.mpr hiQ) hui.2.1 hprob
  have hmean := tendsto_integral_of_L1' _ hiQ.aestronglyMeasurable
    (Eventually.of_forall hiU) hL1
  refine ⟨hiQ, tendsto_nhds_unique hmean ?_⟩
  simpa only [heU] using
    (tendsto_const_nhds : Tendsto (fun _ : ℕ ↦ ∫ ω, M T ω * A T ω ∂P) atTop
      (𝓝 (∫ ω, M T ω * A T ω ∂P)))

end MeasureTheory.Martingale
