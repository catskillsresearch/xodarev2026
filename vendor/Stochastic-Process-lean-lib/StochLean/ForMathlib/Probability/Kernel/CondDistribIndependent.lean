/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import Mathlib.Probability.Kernel.CondDistrib
public import Mathlib.Probability.Independence.Basic

/-! # The conditional law of an independent variable

The actual conditional distribution of a variable independent of its
history agrees almost everywhere, as a measure-valued kernel, with its
original marginal law. Independence gives the genuine product joint law;
native conditional-kernel uniqueness identifies the original `condDistrib`.

Only the conditioned target is standard Borel. Neither the sample space
nor the history space needs that structure, and no equality at arbitrary
history labels is asserted. Evaluation on the original sample space is
already provided by the native `ae_of_ae_map` theorem.
-/

@[expose] public section

open MeasureTheory
open scoped ProbabilityTheory

namespace ProbabilityTheory

/-- Independence identifies the original conditional distribution with
the marginal-law constant kernel on one event of full history measure. -/
theorem condDistrib_ae_eq_const_of_indepFun
    {Ω E K : Type*} {mΩ : MeasurableSpace Ω} {mE : MeasurableSpace E}
    {mK : MeasurableSpace K} [StandardBorelSpace E] [Nonempty E]
    {P : Measure Ω} [IsProbabilityMeasure P] {X : Ω → E} {H : Ω → K}
    (hX : Measurable X) (hH : Measurable H) (hIndep : IndepFun X H P) :
    condDistrib X H P =ᵐ[P.map H] Kernel.const K (P.map X) := by
  apply condDistrib_ae_eq_of_measure_eq_compProd_of_measurable hH hX
  rw [Measure.compProd_const]
  exact hIndep.symm.map_prod_eq_prod_map_map hH.aemeasurable hX.aemeasurable

end ProbabilityTheory
