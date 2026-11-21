/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.Semimartingale.StochasticIntegral.StoppedDifference
public import StochLean.Probability.Process.Semimartingale.StochasticIntegral.Locality
public import StochLean.Probability.Process.Stopping.IntervalLocality

/-! # Protter II.18 corollary: equality on a stochastic interval

The event of agreement only refers to `S < t ≤ T`; no value of the integrand
at `S` is imposed. Right continuity recovers the integrator value at `S`.
All output identities are for stopped processes, so `T = infinity` needs no
terminal random variable or evaluation of a process at infinity.
-/

@[expose] public section

open MeasureTheory
open scoped NNReal

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsFiniteMeasure P]
  {F : Filtration ℝ≥0 mΩ} {X Y H K : ℝ≥0 → Ω → ℝ} {σ τ : Ω → WithTop ℝ≥0}

theorem IsSemimartingale.stochasticIntegral_congr_integrand_on_interval
    (hX : IsSemimartingale X F P) (hF : F.IsUsual P)
    (haH : Adapted F H) (hrH : HasCagladPaths H P)
    (haK : Adapted F K) (hrK : HasCagladPaths K P)
    (hσ : IsStoppingTime F σ) (hτ : IsStoppingTime F τ) :
    ∀ᵐ ω ∂P, σ ω ≤ τ ω →
      (∀ t : ℝ≥0,
        σ ω < (t : WithTop ℝ≥0) → (t : WithTop ℝ≥0) ≤ τ ω → H t ω = K t ω) → ∀ t,
      MeasureTheory.stoppedProcess (hX.stochasticIntegral hF haH hrH) τ t ω -
          MeasureTheory.stoppedProcess (hX.stochasticIntegral hF haH hrH) σ t ω =
        MeasureTheory.stoppedProcess (hX.stochasticIntegral hF haK hrK) τ t ω -
          MeasureTheory.stoppedProcess (hX.stochasticIntegral hF haK hrK) σ t ω := by
  have hloc := hX.stochasticIntegral_congr_integrand_on_paths hF
    (fun t ↦ ((adapted_cutoffIntegrand haH hτ) t).sub ((adapted_cutoffIntegrand haH hσ) t))
    ((hrH.cutoffIntegrand τ).sub (hrH.cutoffIntegrand σ))
    (fun t ↦ ((adapted_cutoffIntegrand haK hτ) t).sub ((adapted_cutoffIntegrand haK hσ) t))
    ((hrK.cutoffIntegrand τ).sub (hrK.cutoffIntegrand σ))
  filter_upwards [hloc, hX.stochasticIntegral_cutoff_difference hF haH hrH hσ hτ,
    hX.stochasticIntegral_cutoff_difference hF haK hrK hσ hτ] with ω hlocal hHdiff hKdiff
  intro hστ hHK t
  exact (hHdiff t).symm.trans
    ((hlocal (fun s ↦ cutoffIntegrand_sub_congr_on_interval hστ hHK s) t).trans (hKdiff t))

theorem IsSemimartingale.stochasticIntegral_congr_integrator_on_interval
    (hX : IsSemimartingale X F P) (hY : IsSemimartingale Y F P) (hF : F.IsUsual P)
    (ha : Adapted F H) (hr : HasCagladPaths H P)
    (hσ : IsStoppingTime F σ) (hτ : IsStoppingTime F τ) :
    ∀ᵐ ω ∂P, σ ω < τ ω →
      (∀ t : ℝ≥0,
        σ ω < (t : WithTop ℝ≥0) → (t : WithTop ℝ≥0) ≤ τ ω → X t ω = Y t ω) → ∀ t,
      MeasureTheory.stoppedProcess (hX.stochasticIntegral hF ha hr) τ t ω -
          MeasureTheory.stoppedProcess (hX.stochasticIntegral hF ha hr) σ t ω =
        MeasureTheory.stoppedProcess (hY.stochasticIntegral hF ha hr) τ t ω -
          MeasureTheory.stoppedProcess (hY.stochasticIntegral hF ha hr) σ t ω := by
  have hZ := (hX.stoppedProcess hF hτ).sub (hX.stoppedProcess hF hσ)
  have hloc := hZ.stochasticIntegral_congr_integrator_on_paths
    ((hY.stoppedProcess hF hτ).sub (hY.stoppedProcess hF hσ)) hF ha hr
  filter_upwards [hloc, hX.stochasticIntegral_stopped_difference hF ha hr hσ hτ,
    hY.stochasticIntegral_stopped_difference hF ha hr hσ hτ,
    hX.hasCadlagPaths, hY.hasCadlagPaths] with ω hlocal hXdiff hYdiff hXω hYω
  intro hστ hXY t
  exact (hXdiff t).symm.trans
    ((hlocal (fun s ↦ stoppedProcess_sub_congr_on_interval hXω.1 hYω.1 hστ hXY s) t).trans
      (hYdiff t))

/-- The path-agreement assertion of the corollary to Protter II.18. -/
theorem IsSemimartingale.stochasticIntegral_congr_on_interval
    (hX : IsSemimartingale X F P) (hY : IsSemimartingale Y F P) (hF : F.IsUsual P)
    (haH : Adapted F H) (hrH : HasCagladPaths H P)
    (haK : Adapted F K) (hrK : HasCagladPaths K P)
    (hσ : IsStoppingTime F σ) (hτ : IsStoppingTime F τ) :
    ∀ᵐ ω ∂P, σ ω < τ ω →
      (∀ t : ℝ≥0,
        σ ω < (t : WithTop ℝ≥0) → (t : WithTop ℝ≥0) ≤ τ ω → H t ω = K t ω) →
      (∀ t : ℝ≥0,
        σ ω < (t : WithTop ℝ≥0) → (t : WithTop ℝ≥0) ≤ τ ω → X t ω = Y t ω) → ∀ t,
      MeasureTheory.stoppedProcess (hX.stochasticIntegral hF haH hrH) τ t ω -
          MeasureTheory.stoppedProcess (hX.stochasticIntegral hF haH hrH) σ t ω =
        MeasureTheory.stoppedProcess (hY.stochasticIntegral hF haK hrK) τ t ω -
          MeasureTheory.stoppedProcess (hY.stochasticIntegral hF haK hrK) σ t ω := by
  filter_upwards [hX.stochasticIntegral_congr_integrand_on_interval hF haH hrH haK hrK hσ hτ,
    hX.stochasticIntegral_congr_integrator_on_interval hY hF haK hrK hσ hτ] with ω hHloc hXloc
  intro hστ hHK hXY t
  exact (hHloc hστ.le hHK t).trans (hXloc hστ hXY t)

end ProbabilityTheory
