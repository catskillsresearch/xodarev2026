/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.Poisson.Basic

/-! # Independent real increments of the original Poisson count

The Poisson predicate records independence of natural-number differences.
On every ordered finite grid, its common almost-sure monotonicity identifies
their real casts with the actual real differences. Measurable postcomposition
and almost-sure congruence then give the native real independent-increments
property, without introducing a filtration or any extra moment hypothesis.
-/

@[expose] public section

open MeasureTheory
open scoped NNReal

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
  {N : ℝ≥0 → Ω → ℕ} {rate : ℝ≥0}

/-- The real-valued original Poisson count has independent increments;
monotonicity justifies each conversion of natural subtraction to real subtraction. -/
theorem IsPoissonProcess.hasIndepIncrements_real (hN : IsPoissonProcess N rate P) :
    HasIndepIncrements (fun t ω ↦ (N t ω : ℝ)) P := by
  intro n t ht
  have hi := (hN.indepIncrements n t ht).comp (fun _ k ↦ (k : ℝ))
    (fun _ ↦ measurable_of_countable (fun k : ℕ ↦ (k : ℝ)))
  apply (iIndepFun_congr ?_).mp hi
  intro i
  filter_upwards [hN.monotonePaths] with ω hω
  change ((N (t i.succ) ω - N (t i.castSucc) ω : ℕ) : ℝ) =
    (N (t i.succ) ω : ℝ) - (N (t i.castSucc) ω : ℝ)
  exact Nat.cast_sub (hω (ht i.castSucc_le_succ))

end ProbabilityTheory
