/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.Semimartingale.StochasticIntegral.InitialValue
public import StochLean.Probability.Process.Semimartingale.StochasticIntegral.Jump
public import StochLean.Probability.Process.Semimartingale.StochasticIntegral.Algebra
public import StochLean.Probability.Process.Semimartingale.StochasticIntegral.IntegratorInvariance
public import StochLean.Probability.Process.Measurability.LeftLimit
public import StochLean.Probability.Process.Path.LeftLimitOperations

/-! # The canonical raw quadratic variation of a semimartingale

The source definition is `X² - 2 (X₋ . X)`. It retains the original initial
square and uses only the previously constructed Chapter II integral. There is
no bracket for an arbitrary process outside the semimartingale domain, and no
separate zero-start or continuous-martingale bracket is constructed here.
-/

@[expose] public section

open MeasureTheory
open scoped NNReal

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsFiniteMeasure P]
  {F : Filtration ℝ≥0 mΩ} {X Y : ℝ≥0 → Ω → ℝ}

noncomputable def IsSemimartingale.quadraticVariation
    (hX : IsSemimartingale X F P) (hF : F.IsUsual P) : ℝ≥0 → Ω → ℝ :=
  fun t ω ↦ (X t ω) ^ 2 - 2 *
    hX.stochasticIntegral hF (hX.adapted.leftLimitProcess_of_usual hF hX.hasCadlagPaths)
      hX.hasCadlagPaths.hasCagladPaths_leftLimitProcess t ω

theorem IsSemimartingale.quadraticVariation_proof_irrel
    (hX hX' : IsSemimartingale X F P) (hF hF' : F.IsUsual P) :
    hX.quadraticVariation hF = hX'.quadraticVariation hF' := rfl

theorem IsSemimartingale.adapted_quadraticVariation
    (hX : IsSemimartingale X F P) (hF : F.IsUsual P) :
    Adapted F (hX.quadraticVariation hF) := by
  intro t
  exact (hX.adapted t).pow_const 2 |>.sub
    ((hX.adapted_stochasticIntegral hF
      (hX.adapted.leftLimitProcess_of_usual hF hX.hasCadlagPaths)
      hX.hasCadlagPaths.hasCagladPaths_leftLimitProcess t).const_mul 2)

theorem IsSemimartingale.hasCadlagPaths_quadraticVariation
    (hX : IsSemimartingale X F P) (hF : F.IsUsual P) :
    HasCadlagPaths (hX.quadraticVariation hF) P := by
  have hJ := hX.hasCadlagPaths_stochasticIntegral hF
    (hX.adapted.leftLimitProcess_of_usual hF hX.hasCadlagPaths)
    hX.hasCadlagPaths.hasCagladPaths_leftLimitProcess
  exact (hX.hasCadlagPaths.continuous_comp (continuous_id.pow 2)).sub
    (hJ.continuous_comp (continuous_const.mul continuous_id))

theorem IsSemimartingale.quadraticVariation_zero_ae
    (hX : IsSemimartingale X F P) (hF : F.IsUsual P) :
    hX.quadraticVariation hF 0 =ᵐ[P] fun ω ↦ (X 0 ω) ^ 2 := by
  filter_upwards [hX.stochasticIntegral_zero_ae hF
    (hX.adapted.leftLimitProcess_of_usual hF hX.hasCadlagPaths)
    hX.hasCadlagPaths.hasCagladPaths_leftLimitProcess] with ω hω
  simp only [leftLimitProcess_zero, Pi.zero_apply, zero_mul] at hω
  simp only [quadraticVariation, hω, mul_zero, sub_zero]

theorem IsSemimartingale.jumpProcess_quadraticVariation
    (hX : IsSemimartingale X F P) (hF : F.IsUsual P) :
    Indistinguishable (jumpProcess (hX.quadraticVariation hF))
      (fun t ω ↦ (jumpProcess X t ω) ^ 2) P := by
  let ha := hX.adapted.leftLimitProcess_of_usual hF hX.hasCadlagPaths
  let hr := hX.hasCadlagPaths.hasCagladPaths_leftLimitProcess
  let J := hX.stochasticIntegral hF ha hr
  filter_upwards [hX.hasCadlagPaths, hX.jumpProcess_stochasticIntegral hF ha hr]
    with ω hXω hJjump t
  have hJω : IsCadlagPath (J · ω) := hX.isCadlagPath_stochasticIntegral hF ha hr ω
  have hsq : IsCadlagPath (fun u ↦ (X u ω) ^ 2) :=
    hXω.continuous_comp (continuous_id.pow 2)
  have hmul : IsCadlagPath (fun u ↦ (2 : ℝ) * J u ω) :=
    hJω.continuous_comp (continuous_const.mul continuous_id)
  change jumpProcess ((fun u v ↦ (X u v) ^ 2) - (fun u v ↦ 2 * J u v)) t ω = _
  rw [IsCadlagPath.jumpProcess_sub (X := fun u v ↦ (X u v) ^ 2)
    (Y := fun u v ↦ 2 * J u v) (ω := ω) hsq hmul t,
    hXω.jumpProcess_sq t, hJω.jumpProcess_const_mul 2 t]
  change (X t ω) ^ 2 - (leftLimitProcess X t ω) ^ 2 -
    2 * jumpProcess (hX.stochasticIntegral hF ha hr) t ω = _
  rw [hJjump t]
  simp only [jumpProcess, Pi.sub_apply]
  ring

theorem IsSemimartingale.quadraticVariation_congr
    (hX : IsSemimartingale X F P) (hY : IsSemimartingale Y F P) (hF : F.IsUsual P)
    (hXY : Indistinguishable X Y P) :
    Indistinguishable (hX.quadraticVariation hF) (hY.quadraticVariation hF) P := by
  let haX := hX.adapted.leftLimitProcess_of_usual hF hX.hasCadlagPaths
  let hrX := hX.hasCadlagPaths.hasCagladPaths_leftLimitProcess
  let haY := hY.adapted.leftLimitProcess_of_usual hF hY.hasCadlagPaths
  let hrY := hY.hasCadlagPaths.hasCagladPaths_leftLimitProcess
  have hi := (hX.stochasticIntegral_congr_integrator hY hF haX hrX hXY).trans
    (hY.stochasticIntegral_congr_integrand hF haX hrX haY hrY hXY.leftLimitProcess)
  filter_upwards [hXY, hi] with ω hω hiω t
  change (X t ω) ^ 2 - 2 * hX.stochasticIntegral hF haX hrX t ω =
    (Y t ω) ^ 2 - 2 * hY.stochasticIntegral hF haY hrY t ω
  rw [hω t, hiω t]

end ProbabilityTheory
