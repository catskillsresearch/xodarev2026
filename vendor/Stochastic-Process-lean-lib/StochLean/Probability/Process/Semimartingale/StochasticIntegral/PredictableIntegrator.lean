/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.Semimartingale.StochasticIntegral
public import StochLean.Probability.Process.Semimartingale.SimplePredictable.PredictableIntegrator
public import StochLean.Probability.Process.UCP.PredictableVersion

/-! # A predictable integrator gives a predictable version of its integral

The original source-simple approximations have predictable actual elementary
integral processes. Their established UCP convergence to the sole selected
Chapter II integral gives an indistinguishable predictable version. Cadlag
paths transfer on the same common event; the selected integral's arbitrary
exceptional trajectories are not asserted predictable.

The result uses the original adapted AE-caglad integrand domain and retains
its initial product. Neither finite variation of the integrator nor a
coefficient bound or an initial moment is assumed. This does not enlarge
the stochastic-integral domain to all predictable integrands.
-/

@[expose] public section

open MeasureTheory Filter
open scoped NNReal

namespace ProbabilityTheory.IsSemimartingale

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsFiniteMeasure P]
  {F : Filtration ℝ≥0 mΩ} {X H : ℝ≥0 → Ω → ℝ}

/-- Predictability is obtained for a genuine version of the actual selected
integral, not imposed as an additional certificate on that integral. -/
theorem exists_predictable_stochasticIntegral_of_predictable
    (hX : IsSemimartingale X F P) (hpX : IsStronglyPredictable F X) (hF : F.IsUsual P)
    (ha : Adapted F H) (hc : HasCagladPaths H P) :
    ∃ J : ℝ≥0 → Ω → ℝ, Indistinguishable (hX.stochasticIntegral hF ha hc) J P ∧
      IsStronglyPredictable F J ∧ HasCadlagPaths J P := by
  obtain ⟨S, hS, huS⟩ := exists_simplePredictable_tendstoUCP ha hF hc
  have hu := hX.tendstoUCP_stochasticIntegral_of_simple hF ha hc hS huS
  obtain ⟨J, he, hpJ⟩ := hu.exists_predictable_indistinguishable
    (fun n ↦ (hS n).isStronglyPredictable_elementaryIntegralProcess hpX)
  exact ⟨J, he, hpJ, (hX.hasCadlagPaths_stochasticIntegral hF ha hc).congr he⟩

end ProbabilityTheory.IsSemimartingale
