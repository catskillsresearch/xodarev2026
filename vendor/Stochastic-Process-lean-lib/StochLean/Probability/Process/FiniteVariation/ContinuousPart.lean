/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.FiniteVariation.StieltjesRealization
public import StochLean.ForMathlib.MeasureTheory.MeasurableStieltjesContinuousPart

/-! # Adaptedness of the continuous component of a random Stieltjes path -/

@[expose] public section

open MeasureTheory StochLean
open scoped NNReal

namespace ProbabilityTheory

theorem adapted_stieltjesContinuousPart
    {Ω : Type*} {mΩ : MeasurableSpace Ω} {F : Filtration ℝ≥0 mΩ}
    {B : Ω → StieltjesFunction ℝ≥0} (hB : Adapted F (fun t ω ↦ B ω t)) :
    Adapted F (fun t ω ↦ stieltjesContinuousPart (B ω) t) := by
  intro T
  let : MeasurableSpace Ω := F T
  exact measurable_stieltjesContinuousPart_of_measurable_upTo T
    (fun t ht ↦ (hB t).mono (F.mono ht) le_rfl)

end ProbabilityTheory
