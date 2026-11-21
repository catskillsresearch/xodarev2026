/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Brownian.DeterministicReflection
public import Mathlib.Probability.Process.FiniteDimensionalLaws

/-! # Brownian reflection on the coordinate-product law

Coordinate measurability is explicit. We do not infer joint almost-everywhere measurability
of an uncountable product from individually almost-everywhere measurable coordinates.
-/

@[expose] public section

open MeasureTheory
open scoped NNReal

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
  {B C : ℝ≥0 → Ω → ℝ}

theorem IsPreBrownianReal.identDistrib_process (hB : IsPreBrownianReal B P)
    (hC : IsPreBrownianReal C P) (hBm : ∀ t, Measurable (B t))
    (hCm : ∀ t, Measurable (C t)) :
    IdentDistrib (fun ω ↦ (B · ω)) (fun ω ↦ (C · ω)) P P := by
  let : IsProbabilityMeasure P := (hB.hasLaw_eval 0).isProbabilityMeasure
  apply (identDistrib_iff_forall_finset_identDistrib
    (measurable_pi_lambda _ hBm).aemeasurable
    (measurable_pi_lambda _ hCm).aemeasurable).mpr
  exact fun I ↦ (hB.hasLaw I).identDistrib (hC.hasLaw I)

theorem measurable_flipInterval (hBm : ∀ t, Measurable (B t)) (a b t : ℝ≥0) :
    Measurable (flipInterval B a b t) :=
  (hBm t).sub (((hBm (min t b)).sub (hBm (min t a))).const_mul 2)

theorem IsPreBrownianReal.identDistrib_flipInterval (hB : IsPreBrownianReal B P)
    (hBm : ∀ t, Measurable (B t)) {a b : ℝ≥0} (hab : a ≤ b) :
    IdentDistrib (fun ω ↦ (B · ω))
      (fun ω ↦ (ProbabilityTheory.flipInterval B a b · ω)) P P :=
  hB.identDistrib_process (hB.flipInterval hab) hBm (measurable_flipInterval hBm a b)

end ProbabilityTheory
