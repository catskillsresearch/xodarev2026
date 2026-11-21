/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.Semimartingale.Ito.VectorTaylorError
public import StochLean.Probability.Process.Semimartingale.QuadraticCovariation.WeightedRiemann
public import StochLean.Probability.Process.Partition.Klenke
public import StochLean.Analysis.PathVariation.UniformPartition

/-! # Finite-dimensional cadlag Ito identity with raw mixed brackets

All ordered Hessian pairs are included. The actual jump remainder is
absolutely summable, and the equality holds on one event for all finite
times. No moments or global derivative bounds are required.
-/

@[expose] public section

open MeasureTheory Filter Set Finset StochLean
open scoped NNReal

namespace ProbabilityTheory

variable {Ω ι : Type*} [Fintype ι] [DecidableEq ι] {mΩ : MeasurableSpace Ω}
  {P : Measure Ω} [IsFiniteMeasure P] {F : Filtration ℝ≥0 mΩ}
  {X : ι → ℝ≥0 → Ω → ℝ} {f : (ι → ℝ) → ℝ}

theorem ito_finiteCoordinates_raw_bracket
    (hX : ∀ i, IsSemimartingale (X i) F P) (hF : F.IsUsual P) (hf : ContDiff ℝ 2 f) :
    let ha₁ : ∀ i, Adapted F (fun t ω ↦ coordinateDeriv f i (fun j ↦ X j t ω)) :=
      fun i t ↦ (contDiff_coordinateDeriv hf i).continuous.measurable.comp
        (@measurable_pi_lambda _ _ _ (F t) _ _ (fun j ↦ (hX j).adapted t))
    let hr₁ := fun i ↦ (HasCadlagPaths.pi (fun j ↦ (hX j).hasCadlagPaths)).continuous_comp
      (contDiff_coordinateDeriv hf i).continuous
    let ha₂ : ∀ i j, Adapted F
        (fun t ω ↦ coordinateSecondDeriv f i j (fun k ↦ X k t ω)) :=
      fun i j t ↦ (continuous_coordinateSecondDeriv hf i j).measurable.comp
        (@measurable_pi_lambda _ _ _ (F t) _ _ (fun k ↦ (hX k).adapted t))
    let hr₂ := fun i j ↦ (HasCadlagPaths.pi (fun k ↦ (hX k).hasCadlagPaths)).continuous_comp
      (continuous_coordinateSecondDeriv hf i j)
    Indistinguishable (fun t ω ↦ f (fun i ↦ X i t ω) - f (fun i ↦ X i 0 ω))
      (fun t ω ↦ (∑ i, (hX i).stochasticIntegral hF
          ((ha₁ i).leftLimitProcess_of_usual hF (hr₁ i))
          (hr₁ i).hasCagladPaths_leftLimitProcess t ω) +
        (1 / 2 : ℝ) * (∑ i, ∑ j,
          ((hX i).isSemimartingale_quadraticCovariation (hX j) hF).stochasticIntegral hF
            ((ha₂ i j).leftLimitProcess_of_usual hF (hr₂ i j))
            (hr₂ i j).hasCagladPaths_leftLimitProcess t ω) +
        ∑' s : Ioc 0 t,
          frechetSecondOrderRemainder f (fun i ↦ leftLimitProcess (X i) s ω)
            (fun i ↦ X i s ω)) P := by
  dsimp only
  let ha₁ : ∀ i, Adapted F (fun t ω ↦ coordinateDeriv f i (fun j ↦ X j t ω)) :=
    fun i t ↦ (contDiff_coordinateDeriv hf i).continuous.measurable.comp
      (@measurable_pi_lambda _ _ _ (F t) _ _ (fun j ↦ (hX j).adapted t))
  let hr₁ := fun i ↦ (HasCadlagPaths.pi (fun j ↦ (hX j).hasCadlagPaths)).continuous_comp
    (contDiff_coordinateDeriv hf i).continuous
  let ha₂ : ∀ i j, Adapted F
      (fun t ω ↦ coordinateSecondDeriv f i j (fun k ↦ X k t ω)) :=
    fun i j t ↦ (continuous_coordinateSecondDeriv hf i j).measurable.comp
      (@measurable_pi_lambda _ _ _ (F t) _ _ (fun k ↦ (hX k).adapted t))
  let hr₂ := fun i j ↦ (HasCadlagPaths.pi (fun k ↦ (hX k).hasCadlagPaths)).continuous_comp
    (continuous_coordinateSecondDeriv hf i j)
  let π : ℕ → StoppingTimePartition F := fun n ↦ StoppingTimePartition.deterministic F
    ((LocallyFinitePartition.dyadic n).restrict (n : ℝ≥0))
  have hπ : StoppingTimePartition.IsTendingToIdentity π P :=
    StoppingTimePartition.isTendingToIdentity_of_klenke
      LocallyFinitePartition.dyadic_admissible tendsto_natCast_atTop_atTop
  have h₁ := TendstoUCP.sum univ (fun i _ ↦
    (hX i).tendstoUCP_leftRiemannSum_leftLimit_of_cadlag hF (ha₁ i) (hr₁ i) hπ)
  have h₂ := TendstoUCP.sum univ (fun i _ ↦ TendstoUCP.sum univ (fun j _ ↦
    (hX i).tendstoUCP_weightedQuadraticCovariationSum (hX j) hF (ha₂ i j) (hr₂ i j) hπ))
  have hu := (((hπ.tendstoUCP_min_terminal (fun t ω ↦ f (fun i ↦ X i t ω))).sub
    (tendstoUCP_const atTop (fun _ ω ↦ f (fun i ↦ X i 0 ω)))).sub h₁).sub
      (h₂.smul (1 / 2 : ℝ))
  have he := frechetTaylorError_limit_eq_jump_series hX hF hf hπ
    (hu.congr_left (fun n ↦ ae_of_all _ (fun ω t ↦ by
      rw [(π n).frechetTaylorErrorProcess_eq_riemann]
      simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_apply])))
  filter_upwards [he] with ω hω t
  have h := hω t
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_apply] at h
  linarith only [h]

end ProbabilityTheory
