/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.UCP
public import StochLean.ForMathlib.MeasureTheory.Measure.AbsolutelyContinuousConvergence

/-! # UCP under an absolutely continuous finite measure

The event-measure transfer works even without path regularity or measurable compact
suprema. Its proof uses measurable covers, not an outer-measure continuity assumption.
-/

@[expose] public section

open MeasureTheory Filter
open scoped NNReal

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P Q : Measure Ω} [IsFiniteMeasure Q]
  {X : ℕ → ℝ≥0 → Ω → ℝ} {Y : ℝ≥0 → Ω → ℝ}

theorem TendstoUCP.absolutelyContinuous (h : TendstoUCP P X atTop Y) (hQP : Q ≪ P) :
    TendstoUCP Q X atTop Y :=
  fun T ε hε ↦ hQP.tendsto_measure_zero (h T ε hε)

end ProbabilityTheory
