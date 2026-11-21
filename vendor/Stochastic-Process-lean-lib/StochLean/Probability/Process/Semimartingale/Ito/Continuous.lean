/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.Semimartingale.Ito.ContinuousTaylorError
public import StochLean.Probability.Process.Semimartingale.QuadraticVariation.WeightedRiemann

/-! # The continuous-semimartingale Itô formula (Protter II.32)

The proof uses exact finite Taylor sums and the existing random-partition
integral limits. Both integrands are source left limits, hence zero at time
zero; the raw bracket retains its original initial value `X₀²`.
No boundedness or moment assumptions on `X`, `f'`, or `f''` are imposed.
-/

@[expose] public section

open MeasureTheory Filter StochLean
open scoped NNReal

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsFiniteMeasure P]
  {F : Filtration ℝ≥0 mΩ} {X : ℝ≥0 → Ω → ℝ} {f : ℝ → ℝ}

theorem IsSemimartingale.ito_of_continuous
    (hX : IsSemimartingale X F P) (hF : F.IsUsual P)
    (hc : HasContinuousPaths X P) (hf : ContDiff ℝ 2 f) :
    let hd : ContDiff ℝ 1 (deriv f) := hf.deriv'
    let ha₁ : Adapted F (fun t ω ↦ deriv f (X t ω)) :=
      fun t ↦ hd.continuous.measurable.comp (hX.adapted t)
    let hr₁ := hX.hasCadlagPaths.continuous_comp hd.continuous
    let ha₂ : Adapted F (fun t ω ↦ deriv (deriv f) (X t ω)) :=
      fun t ↦ hd.continuous_deriv_one.measurable.comp (hX.adapted t)
    let hr₂ := hX.hasCadlagPaths.continuous_comp hd.continuous_deriv_one
    Indistinguishable (fun t ω ↦ f (X t ω) - f (X 0 ω))
      (hX.stochasticIntegral hF (ha₁.leftLimitProcess_of_usual hF hr₁)
          hr₁.hasCagladPaths_leftLimitProcess +
        (1 / 2 : ℝ) • (hX.isSemimartingale_quadraticVariation hF).stochasticIntegral hF
          (ha₂.leftLimitProcess_of_usual hF hr₂) hr₂.hasCagladPaths_leftLimitProcess) P := by
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
  have he := hX.quadraticTaylorError_limit_zero_of_continuous hF hc hf hπ
    (hu.congr_left (fun n ↦ ae_of_all _ (fun ω t ↦ by
      rw [(π n).quadraticTaylorErrorProcess_eq_riemann]
      rfl)))
  filter_upwards [he] with ω hω t
  have h := hω t
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at h
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  linarith only [h]

end ProbabilityTheory
