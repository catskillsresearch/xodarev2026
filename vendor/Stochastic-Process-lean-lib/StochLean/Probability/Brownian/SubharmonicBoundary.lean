/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.ForMathlib.Probability.GaussianCriticalExponential
public import Mathlib.Probability.BrownianMotion.Basic
public import Mathlib.Probability.Martingale.Basic

/-! # An integrability obstruction to an unguarded subharmonic assertion

For every real Brownian motion, exp(B_1^2/2) is not integrable. Consequently
the smooth subharmonic composition exp(B_t^2/2) cannot be a true submartingale
in any filtration. A local conclusion or extra integrability is indispensable.
-/

@[expose] public section

open MeasureTheory
open scoped NNReal

namespace ProbabilityTheory

theorem IsBrownianReal.not_integrable_exp_half_sq_at_one
    {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
    {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P) :
    ¬ Integrable (fun ω ↦ Real.exp ((B 1 ω) ^ 2 / 2)) P := by
  intro h
  apply not_integrable_exp_half_sq_gaussianReal
  have hl := hB.toIsPreBrownianReal.hasLaw_eval 1
  rw [← hl.map_eq]
  exact (integrable_map_measure (by fun_prop) hl.aemeasurable).2 h

theorem IsBrownianReal.not_submartingale_exp_half_sq
    {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
    {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P) (F : Filtration ℝ≥0 mΩ) :
    ¬ Submartingale (fun t ω ↦ Real.exp ((B t ω) ^ 2 / 2)) F P :=
  fun h ↦ hB.not_integrable_exp_half_sq_at_one (h.integrable 1)

end ProbabilityTheory
