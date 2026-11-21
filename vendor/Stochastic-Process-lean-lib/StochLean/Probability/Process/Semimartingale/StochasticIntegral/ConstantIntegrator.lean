/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.Semimartingale.StochasticIntegral.Stopping
public import StochLean.Probability.Process.Semimartingale.StochasticIntegral.InitialValue
public import StochLean.Probability.Process.Semimartingale.StochasticIntegral.IntegratorInvariance

/-! # The initial product for a constant random integrator

The source integral of a random constant is not automatically zero. It equals
the initial integrand times that constant, without integrability assumptions.
-/

@[expose] public section

open MeasureTheory Filter
open scoped NNReal

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsFiniteMeasure P]
  {F : Filtration ℝ≥0 mΩ} {Z : Ω → ℝ} {H : ℝ≥0 → Ω → ℝ}

theorem stochasticIntegral_const_initial (hZ : Measurable[F 0] Z) (hF : F.IsUsual P)
    (ha : Adapted F H) (hr : HasCagladPaths H P) :
    Indistinguishable ((isSemimartingale_const_initial hZ).stochasticIntegral hF ha hr)
      (fun _ ω ↦ H 0 ω * Z ω) P := by
  let hC := isSemimartingale_const_initial (P := P) hZ
  have hτ := isStoppingTime_const F (0 : ℝ≥0)
  have he : Indistinguishable
      (MeasureTheory.stoppedProcess (fun _ : ℝ≥0 ↦ Z) (fun _ ↦ (0 : WithTop ℝ≥0)))
      (fun _ : ℝ≥0 ↦ Z) P := Eventually.of_forall fun _ _ ↦ rfl
  have hsame := (hC.stoppedProcess hF hτ).stochasticIntegral_congr_integrator hC hF ha hr he
  have hstop := hsame.symm.trans (hC.stochasticIntegral_stoppedProcess hF ha hr hτ)
  filter_upwards [hstop, hC.stochasticIntegral_zero_ae hF ha hr] with ω hs hz t
  apply (hs t).trans
  change hC.stochasticIntegral hF ha hr (min (t : WithTop ℝ≥0) 0).untopA ω = _
  rw [min_eq_right (show (0 : WithTop ℝ≥0) ≤ t from bot_le)]
  exact hz

theorem stochasticIntegral_const_initial_of_zero_initial_integrand
    (hZ : Measurable[F 0] Z) (hF : F.IsUsual P)
    (ha : Adapted F H) (hr : HasCagladPaths H P) (h0 : H 0 =ᵐ[P] 0) :
    Indistinguishable ((isSemimartingale_const_initial hZ).stochasticIntegral hF ha hr) 0 P := by
  filter_upwards [stochasticIntegral_const_initial hZ hF ha hr, h0] with ω he hω t
  simpa only [hω, Pi.zero_apply, zero_mul] using he t

end ProbabilityTheory
