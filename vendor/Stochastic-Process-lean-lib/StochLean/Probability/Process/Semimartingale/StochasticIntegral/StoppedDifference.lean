/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.Semimartingale.StochasticIntegral.IntegratorAlgebra
public import StochLean.Probability.Process.Semimartingale.StochasticIntegral.Stopping

/-! # Stopped differences and left-open interval integration

The two representations use only the canonical stopped-process and closed-cutoff
owners. Their initial terms cancel. No ordering or finiteness of the stopping
times is needed for these algebraic identities.
-/

@[expose] public section

open MeasureTheory
open scoped NNReal

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsFiniteMeasure P]
  {F : Filtration ℝ≥0 mΩ} {X H : ℝ≥0 → Ω → ℝ} {σ τ : Ω → WithTop ℝ≥0}

theorem IsSemimartingale.stochasticIntegral_stopped_difference
    (hX : IsSemimartingale X F P) (hF : F.IsUsual P)
    (ha : Adapted F H) (hr : HasCagladPaths H P)
    (hσ : IsStoppingTime F σ) (hτ : IsStoppingTime F τ) :
    Indistinguishable
      (((hX.stoppedProcess hF hτ).sub (hX.stoppedProcess hF hσ)).stochasticIntegral hF ha hr)
      (MeasureTheory.stoppedProcess (hX.stochasticIntegral hF ha hr) τ -
        MeasureTheory.stoppedProcess (hX.stochasticIntegral hF ha hr) σ) P := by
  filter_upwards [(hX.stoppedProcess hF hτ).stochasticIntegral_sub_integrator
    (hX.stoppedProcess hF hσ) hF ha hr, hX.stochasticIntegral_stoppedProcess hF ha hr hτ,
    hX.stochasticIntegral_stoppedProcess hF ha hr hσ] with ω hsub hτJ hσJ t
  exact (hsub t).trans (congrArg₂ (· - ·) (hτJ t) (hσJ t))

theorem IsSemimartingale.stochasticIntegral_cutoff_difference
    (hX : IsSemimartingale X F P) (hF : F.IsUsual P)
    (ha : Adapted F H) (hr : HasCagladPaths H P)
    (hσ : IsStoppingTime F σ) (hτ : IsStoppingTime F τ) :
    Indistinguishable
      (hX.stochasticIntegral hF
        (fun t ↦ ((adapted_cutoffIntegrand ha hτ) t).sub ((adapted_cutoffIntegrand ha hσ) t))
        ((hr.cutoffIntegrand τ).sub (hr.cutoffIntegrand σ)))
      (MeasureTheory.stoppedProcess (hX.stochasticIntegral hF ha hr) τ -
        MeasureTheory.stoppedProcess (hX.stochasticIntegral hF ha hr) σ) P := by
  filter_upwards [hX.stochasticIntegral_sub hF
    (adapted_cutoffIntegrand ha hτ) (hr.cutoffIntegrand τ)
    (adapted_cutoffIntegrand ha hσ) (hr.cutoffIntegrand σ),
    hX.stochasticIntegral_cutoff hF ha hr hτ,
    hX.stochasticIntegral_cutoff hF ha hr hσ] with ω hsub hτJ hσJ t
  exact (hsub t).trans (congrArg₂ (· - ·) (hτJ t) (hσJ t))

end ProbabilityTheory
