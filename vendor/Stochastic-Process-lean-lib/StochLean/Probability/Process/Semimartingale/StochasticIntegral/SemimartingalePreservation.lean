/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.Semimartingale.StochasticIntegral.SimpleAssociativity
public import StochLean.Probability.Process.Semimartingale.StochasticIntegral.Continuity
public import StochLean.Probability.Process.UCP.UniformInput

/-! # Protter II.19: stochastic integration preserves semimartingales

Uniformly vanishing simple test processes multiplied by the fixed caglad
integrand vanish in UCP. Continuity of the already constructed integral and
simple-outer associativity prove the good-integrator property at each finite
horizon. No classical decomposition or operator-closure assumption is used.
-/

@[expose] public section

open MeasureTheory Filter
open scoped NNReal ENNReal Topology

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsFiniteMeasure P]
  {F : Filtration ℝ≥0 mΩ} {X H : ℝ≥0 → Ω → ℝ}

theorem IsSemimartingale.stochasticIntegral_zero_integrand
    (hX : IsSemimartingale X F P) (hF : F.IsUsual P) :
    Indistinguishable (hX.stochasticIntegral hF (IsSimplePredictable.zero F).adapted
      ((IsSimplePredictable.zero F).hasCagladPaths P)) 0 P := by
  have heq : (IsSimplePredictable.zero F).elementaryIntegralProcess X = 0 := by
    funext t
    exact IsSimplePredictable.elementaryIntegral_zero F _
  simpa only [heq] using hX.stochasticIntegral_indistinguishable_of_simple hF
    (IsSimplePredictable.zero F).adapted ((IsSimplePredictable.zero F).hasCagladPaths P)
    (IsSimplePredictable.zero F)

theorem IsSemimartingale.isSemimartingale_stochasticIntegral
    (hX : IsSemimartingale X F P) (hF : F.IsUsual P)
    (ha : Adapted F H) (hr : HasCagladPaths H P) :
    IsSemimartingale (hX.stochasticIntegral hF ha hr) F P := by
  let Y := hX.stochasticIntegral hF ha hr
  have haY : Adapted F Y := hX.adapted_stochasticIntegral hF ha hr
  have hrY : HasCadlagPaths Y P := hX.hasCadlagPaths_stochasticIntegral hF ha hr
  intro T
  refine ⟨?_, hrY.stoppedProcess (fun _ ↦ (T : WithTop ℝ≥0)), ?_⟩
  · intro t
    change Measurable[F t] (Y (min t T))
    exact (haY _).mono (F.mono (min_le_left t T)) le_rfl
  · intro G hG huG
    have hu0 : TendstoUCP P G atTop 0 := tendstoUCP_of_tendstoUniformly huG
    have huGH := hu0.mul_right_of_caglad
      (fun n t ↦ ((hG n).adapted t).mono (F.le t) le_rfl)
      (fun _ ↦ measurable_const) (fun t ↦ (ha t).mono (F.le t) le_rfl)
      (fun n ↦ (hG n).hasCagladPaths P) ((IsSimplePredictable.zero F).hasCagladPaths P) hr
    rw [zero_mul] at huGH
    have huJ := hX.tendstoUCP_stochasticIntegral hF (IsSimplePredictable.zero F).adapted
      ((IsSimplePredictable.zero F).hasCagladPaths P)
      (fun n t ↦ ((hG n).adapted t).mul (ha t))
      (fun n ↦ ((hG n).hasCagladPaths P).mul hr) huGH
    have huJ0 := huJ.congr_right (hX.stochasticIntegral_zero_integrand hF)
    have huY : TendstoUCP P (fun n ↦ (hG n).elementaryIntegralProcess Y) atTop 0 :=
      huJ0.congr_left (fun n ↦
        (hX.elementaryIntegralProcess_stochasticIntegral hF (hG n) ha hr).symm)
    exact huY.fixedTime T

end ProbabilityTheory
