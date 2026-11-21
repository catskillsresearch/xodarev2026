/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.Semimartingale.StochasticIntegral.InitialValue
public import StochLean.Probability.Process.Semimartingale.StochasticIntegral.Stopping
public import StochLean.Probability.Process.Semimartingale.StochasticIntegral.Subtraction
public import StochLean.Probability.Process.Measurability.LeftLimit

/-! # Separating the initial product from increment-only integration

Cutting an integrand off at time zero leaves only its initial product. For a
continuous integrand its source left-limit process is the original integrand
with the initial spike removed, not the original integrand at every time.
-/

@[expose] public section

open MeasureTheory Set
open scoped NNReal

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsFiniteMeasure P]
  {F : Filtration ℝ≥0 mΩ} {X H : ℝ≥0 → Ω → ℝ}

theorem IsSemimartingale.stochasticIntegral_cutoff_zero
    (hX : IsSemimartingale X F P) (hF : F.IsUsual P)
    (ha : Adapted F H) (hr : HasCagladPaths H P) :
    Indistinguishable
      (hX.stochasticIntegral hF (adapted_cutoffIntegrand ha (isStoppingTime_const F 0))
        (hr.cutoffIntegrand (fun _ ↦ (0 : WithTop ℝ≥0))))
      (fun _ ω ↦ H 0 ω * X 0 ω) P := by
  filter_upwards [hX.stochasticIntegral_cutoff hF ha hr (isStoppingTime_const F 0),
    hX.stochasticIntegral_zero_ae hF ha hr] with ω hc h0 t
  apply (hc t).trans
  change hX.stochasticIntegral hF ha hr (min (t : WithTop ℝ≥0) 0).untopA ω = _
  rw [min_eq_right (show (0 : WithTop ℝ≥0) ≤ t from bot_le)]
  exact h0

theorem IsSemimartingale.stochasticIntegral_leftLimit_of_continuous
    (hX : IsSemimartingale X F P) (hF : F.IsUsual P)
    (ha : Adapted F H) (hc : HasContinuousPaths H P) :
    Indistinguishable
      (hX.stochasticIntegral hF (ha.leftLimitProcess_of_usual hF hc.hasCadlagPaths)
        hc.hasCadlagPaths.hasCagladPaths_leftLimitProcess)
      (fun t ω ↦ hX.stochasticIntegral hF ha hc.hasCagladPaths t ω - H 0 ω * X 0 ω) P := by
  let K := cutoffIntegrand H (fun _ ↦ (0 : WithTop ℝ≥0))
  have haK : Adapted F K := adapted_cutoffIntegrand ha (isStoppingTime_const F 0)
  have hrK : HasCagladPaths K P := hc.hasCagladPaths.cutoffIntegrand _
  have heq : Indistinguishable (leftLimitProcess H) (H - K) P := by
    filter_upwards [hc] with ω hω t
    by_cases ht : t = 0
    · subst t
      simp [K]
    · rw [hω.leftLimitProcess_eq ht]
      have ht' : ¬ (t : WithTop ℝ≥0) ≤ 0 :=
        not_le_of_gt (WithTop.coe_lt_coe.mpr (pos_iff_ne_zero.mpr ht))
      simp only [Pi.sub_apply, K, cutoffIntegrand, if_neg ht', sub_zero]
  have hI := hX.stochasticIntegral_congr_integrand hF
    (ha.leftLimitProcess_of_usual hF hc.hasCadlagPaths)
    hc.hasCadlagPaths.hasCagladPaths_leftLimitProcess
    (fun t ↦ (ha t).sub (haK t)) (hc.hasCagladPaths.sub hrK) heq
  filter_upwards [hI, hX.stochasticIntegral_sub hF ha hc.hasCagladPaths haK hrK,
    hX.stochasticIntegral_cutoff_zero hF ha hc.hasCagladPaths] with ω he hsub hz t
  exact (he t).trans ((hsub t).trans (congrArg (fun a ↦
    hX.stochasticIntegral hF ha hc.hasCagladPaths t ω - a) (hz t)))

end ProbabilityTheory
