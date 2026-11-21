/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Brownian.Construction
public import StochLean.Probability.Process.Path.Supremum

/-!
# Measurable Brownian path functionals

This file supplies the countable, process-level measurable objects used by the reflection and
last-zero arguments.  It deliberately does not introduce a continuous-path-space hierarchy.

For a continuous path, strict exceedance of a positive level before a deterministic horizon can
be detected at rational nonnegative times.  The countable supremum below is therefore the
measurable representative needed by the reflection principle; the bridge to the uncountable
running supremum is stated separately under path continuity.
-/

@[expose] public section

open Filter MeasureTheory
open scoped ENNReal NNReal Topology

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

variable {P : Measure Ω} {B : ℝ≥0 → Ω → ℝ}

/-- The dense running supremum of the canonical all-path-continuous Brownian representative is a
measurable random variable. -/
theorem IsPreBrownianReal.measurable_denseRunningSupremum_mk
    (hB : IsPreBrownianReal B P) (T : ℝ≥0) :
    Measurable (denseRunningSupremum (hB.mk B) T) :=
  measurable_denseRunningSupremum hB.measurable_mk T

/-- For the canonical Brownian representative, the measurable dense-grid object detects the
genuine uncountable-time strict exceedance pathwise. -/
theorem IsPreBrownianReal.lt_denseRunningSupremum_mk_iff
    (hB : IsPreBrownianReal B P) {T : ℝ≥0} {a : ℝ} (ha : 0 ≤ a) (ω : Ω) :
    ENNReal.ofReal a < denseRunningSupremum (hB.mk B) T ω ↔
      ∃ t : ℝ≥0, t ≤ T ∧ a < hB.mk B t ω :=
  lt_denseRunningSupremum_iff_exists_of_continuous ha (hB.continuous_mk ω)

/-- The same countable/uncountable strict-exceedance bridge holds on the one common continuity
event of an arbitrary Brownian realization. -/
theorem IsBrownianReal.ae_lt_denseRunningSupremum_iff
    (hB : IsBrownianReal B P) {T : ℝ≥0} {a : ℝ} (ha : 0 ≤ a) :
    ∀ᵐ ω ∂P, ENNReal.ofReal a < denseRunningSupremum B T ω ↔
      ∃ t : ℝ≥0, t ≤ T ∧ a < B t ω := by
  filter_upwards [hB.cont] with ω hω
  exact lt_denseRunningSupremum_iff_exists_of_continuous ha hω

end ProbabilityTheory
