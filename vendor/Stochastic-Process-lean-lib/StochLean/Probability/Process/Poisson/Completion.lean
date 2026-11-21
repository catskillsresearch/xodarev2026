/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.Poisson.Basic
public import StochLean.Probability.Independence.FamilyCompletion

/-! # The original Poisson process under genuine measure completion

The original process is unchanged on the genuinely completed sample space.
Its increment laws and joint independent increments are transported using
the actual completion of the original measure, and its common-event path
properties are retained. No second realization or process version is
selected, and no arbitrary information enlargement is allowed.
-/

@[expose] public section

open MeasureTheory
open scoped NNReal

namespace ProbabilityTheory

/-- Genuine completion preserves the original Poisson process, including
all finite joint increment independence and the same common path events. -/
theorem IsPoissonProcess.completion
    {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
    {N : ℝ≥0 → Ω → ℕ} {rate : ℝ≥0} (hN : IsPoissonProcess N rate P) :
    IsPoissonProcess (fun t (ω : NullMeasurableSpace Ω P) ↦ N t ω) rate P.completion := by
  have hm (t : ℝ≥0) : Measurable (fun ω : NullMeasurableSpace Ω P ↦ N t ω) :=
    (hN.aemeasurable t).nullMeasurable
  refine ⟨fun t ↦ (hm t).aemeasurable,
    hN.initial, hN.monotonePaths, hN.rightContinuousPaths, ?_, ?_⟩
  · intro n t ht
    exact (hN.indepIncrements n t ht).completion
  · intro s t hst
    exact (hN.incrementLaw s t hst).completion

end ProbabilityTheory
