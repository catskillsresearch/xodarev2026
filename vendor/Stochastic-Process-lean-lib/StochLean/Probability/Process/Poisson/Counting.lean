/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.Counting.Basic
public import StochLean.Probability.Process.Poisson.QuadraticVariation

/-! # Poisson processes belong to the nonexplosive counting domain

The original Poisson predicate supplies finite natural-valued counts, zero
initial value, monotone paths, and right continuity. Its unit-jump property
is derived, not assumed: the already established actual raw bracket equals
the real counting process, while the bracket jump is the square of the
count's jump. Thus each jump satisfies `j ^ 2 = j` on one event for all times.

This proof uses adaptedness to a chosen usual filtration only to invoke the
existing actual-bracket theorem. No independence from the filtration's past,
initial moment, new path realization, or candidate counting certificate is
required. The counting predicate itself remains filtration-independent.
-/

@[expose] public section

open MeasureTheory Filter
open scoped NNReal

namespace ProbabilityTheory.IsPoissonProcess

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
  {N : ℝ≥0 → Ω → ℕ} {rate : ℝ≥0} {F : Filtration ℝ≥0 mΩ}

/-- The actual Poisson process has no multiple jumps, and hence satisfies
the nonexplosive counting predicate. The filtration is used only by the
already proved raw-bracket identification, not by an added independence axiom. -/
theorem isNonexplosiveCountingProcess (hN : IsPoissonProcess N rate P)
    (hF : F.IsUsual P) (ha : Adapted F N) : IsNonexplosiveCountingProcess N P := by
  refine ⟨hN.aemeasurable, hN.initial, hN.monotonePaths, hN.rightContinuousPaths, ?_⟩
  have he := (hN.quadraticVariation_real_eq hF ha).jumpProcess
  have hj := (hN.isSemimartingale_real hF ha).jumpProcess_quadraticVariation hF
  filter_upwards [he, hj] with ω heω hjω t _ht
  exact eq_zero_or_one_of_sq_eq_self ((hjω t).symm.trans (heω t))

end ProbabilityTheory.IsPoissonProcess
