/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.Semimartingale.StochasticIntegral
public import StochLean.Probability.Process.Semimartingale.AbsoluteContinuity
public import StochLean.Probability.Process.UCP.AbsoluteContinuity

/-! # Protter II.14: invariance under absolutely continuous changes of measure

The target semimartingale property is derived, not assumed. Usual conditions under
the target measure remain explicit: completeness for the source measure does not
imply completeness for an arbitrary absolutely continuous target measure.
-/

@[expose] public section

open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P Q : Measure Ω}
  [IsFiniteMeasure P] [IsFiniteMeasure Q] {F : Filtration ℝ≥0 mΩ}
  {X H : ℝ≥0 → Ω → ℝ}

theorem IsSemimartingale.stochasticIntegral_absolutelyContinuous
    (hX : IsSemimartingale X F P) (hQP : Q ≪ P)
    (hFP : F.IsUsual P) (hFQ : F.IsUsual Q)
    (ha : Adapted F H) (hr : HasCagladPaths H P) :
    Indistinguishable
      ((hX.absolutelyContinuous hQP hFP).stochasticIntegral hFQ ha (hQP.ae_le hr))
      (hX.stochasticIntegral hFP ha hr) Q := by
  obtain ⟨S, hS, huS⟩ := exists_simplePredictable_tendstoUCP ha hFP hr
  apply (hX.absolutelyContinuous hQP hFP).stochasticIntegral_indistinguishable_of_limit
    hFQ ha (hQP.ae_le hr) hS (huS.absolutelyContinuous hQP)
  · exact (hX.tendstoUCP_stochasticIntegral_of_simple hFP ha hr hS huS).absolutelyContinuous hQP
  · exact Eventually.of_forall fun ω ↦ (hX.isCadlagPath_stochasticIntegral hFP ha hr ω).1

end ProbabilityTheory
