/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.Semimartingale.Ito.CadlagTaylorError
public import StochLean.Probability.Process.Semimartingale.QuadraticVariation.WeightedRiemann
public import StochLean.Probability.Process.Partition.Klenke
public import StochLean.Analysis.PathVariation.UniformPartition

/-! # General cadlag Ito identity with the original raw quadratic variation

This is the equivalent raw-bracket form in Protter II.32's proof. Its
absolutely summable jump correction subtracts both first- and second-order
terms. The identity is on one event for all finite times and retains the
source initial convention through zero-starting left-limit integrands.
-/

@[expose] public section

open MeasureTheory Filter Set StochLean
open scoped NNReal

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsFiniteMeasure P]
  {F : Filtration ℝ≥0 mΩ} {X : ℝ≥0 → Ω → ℝ} {f : ℝ → ℝ}

theorem IsSemimartingale.ito_raw_bracket
    (hX : IsSemimartingale X F P) (hF : F.IsUsual P) (hf : ContDiff ℝ 2 f) :
    let hd : ContDiff ℝ 1 (deriv f) := hf.deriv'
    let ha₁ : Adapted F (fun t ω ↦ deriv f (X t ω)) :=
      fun t ↦ hd.continuous.measurable.comp (hX.adapted t)
    let hr₁ := hX.hasCadlagPaths.continuous_comp hd.continuous
    let ha₂ : Adapted F (fun t ω ↦ deriv (deriv f) (X t ω)) :=
      fun t ↦ hd.continuous_deriv_one.measurable.comp (hX.adapted t)
    let hr₂ := hX.hasCadlagPaths.continuous_comp hd.continuous_deriv_one
    Indistinguishable (fun t ω ↦ f (X t ω) - f (X 0 ω))
      (fun t ω ↦ hX.stochasticIntegral hF (ha₁.leftLimitProcess_of_usual hF hr₁)
          hr₁.hasCagladPaths_leftLimitProcess t ω +
        (1 / 2 : ℝ) * (hX.isSemimartingale_quadraticVariation hF).stochasticIntegral hF
          (ha₂.leftLimitProcess_of_usual hF hr₂) hr₂.hasCagladPaths_leftLimitProcess t ω +
        ∑' s : Ioc 0 t, (f (X s ω) - f (leftLimitProcess X s ω) -
          deriv f (leftLimitProcess X s ω) * jumpProcess X s ω -
          deriv (deriv f) (leftLimitProcess X s ω) / 2 * (jumpProcess X s ω) ^ 2)) P := by
  dsimp only
  let hd : ContDiff ℝ 1 (deriv f) := hf.deriv'
  let ha₁ : Adapted F (fun t ω ↦ deriv f (X t ω)) :=
    fun t ↦ hd.continuous.measurable.comp (hX.adapted t)
  let hr₁ := hX.hasCadlagPaths.continuous_comp hd.continuous
  let ha₂ : Adapted F (fun t ω ↦ deriv (deriv f) (X t ω)) :=
    fun t ↦ hd.continuous_deriv_one.measurable.comp (hX.adapted t)
  let hr₂ := hX.hasCadlagPaths.continuous_comp hd.continuous_deriv_one
  let π : ℕ → StoppingTimePartition F := fun n ↦ StoppingTimePartition.deterministic F
    ((LocallyFinitePartition.dyadic n).restrict (n : ℝ≥0))
  have hπ : StoppingTimePartition.IsTendingToIdentity π P :=
    StoppingTimePartition.isTendingToIdentity_of_klenke
      LocallyFinitePartition.dyadic_admissible tendsto_natCast_atTop_atTop
  have h₁ := hX.tendstoUCP_leftRiemannSum_leftLimit_of_cadlag hF ha₁ hr₁ hπ
  have h₂ := hX.tendstoUCP_weightedQuadraticVariationSum hF ha₂ hr₂ hπ
  have hu := (((hπ.tendstoUCP_min_terminal (fun t ω ↦ f (X t ω))).sub
    (tendstoUCP_const atTop (fun _ ω ↦ f (X 0 ω)))).sub h₁).sub (h₂.smul (1 / 2 : ℝ))
  have he := hX.quadraticTaylorError_limit_eq_jump_series hF hf hπ
    (hu.congr_left (fun n ↦ ae_of_all _ (fun ω t ↦ by
      rw [(π n).quadraticTaylorErrorProcess_eq_riemann]
      rfl)))
  filter_upwards [he] with ω hω t
  have h := hω t
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at h
  linarith only [h]

end ProbabilityTheory
