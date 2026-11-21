/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import Mathlib.Probability.Kernel.CondDistrib
public import Mathlib.Probability.Kernel.CompProdEqIff

/-! # Conditional distributions depend on the generated information

Two measurable history variables generating exactly the same sigma algebra
give the same conditional distribution when evaluated at their actual
history values, almost surely. The target is standard Borel, as required by
the native conditional-distribution construction; neither the original
sample space nor either history space needs that assumption.

For each measurable target set, both real conditional masses are the same
conditional expectation. Their actual finite masses agree almost surely.
Finite product-measure extensionality and native kernel uniqueness then give
one common almost-sure equality of measures, not merely a separate event for
each target set. Kernels at arbitrary, unrealized history labels are not
identified, and no new conditional-distribution owner is introduced.
-/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal ProbabilityTheory

namespace ProbabilityTheory

/-- Equal generated information gives equality of the actual evaluated
conditional distributions on one common event, even for different history spaces. -/
theorem condDistrib_comp_ae_eq_of_comap_eq
    {Ω K L E : Type*} {mΩ : MeasurableSpace Ω} {mK : MeasurableSpace K}
    {mL : MeasurableSpace L} {mE : MeasurableSpace E}
    [StandardBorelSpace E] [Nonempty E]
    {P : Measure Ω} [IsFiniteMeasure P]
    {X : Ω → K} {Z : Ω → L} {Y : Ω → E}
    (hX : Measurable X) (hZ : Measurable Z) (hY : Measurable Y)
    (hinfo : MeasurableSpace.comap X mK = MeasurableSpace.comap Z mL) :
    (fun ω ↦ condDistrib Y X P (X ω)) =ᵐ[P]
      fun ω ↦ condDistrib Y Z P (Z ω) := by
  let κ := (condDistrib Y X P).comap X hX
  let η := (condDistrib Y Z P).comap Z hZ
  have he (B : Set E) (hB : MeasurableSet B) :
      (fun ω ↦ κ ω B) =ᵐ[P] fun ω ↦ η ω B := by
    have hx := condDistrib_ae_eq_condExp (μ := P) hX hY hB
    have hz := condDistrib_ae_eq_condExp (μ := P) hZ hY hB
    rw [hinfo] at hx
    filter_upwards [hx, hz] with ω hx hz
    apply (ENNReal.toReal_eq_toReal_iff' (measure_ne_top (κ ω) B)
      (measure_ne_top (η ω) B)).mp
    exact hx.trans hz.symm
  change κ =ᵐ[P] η
  apply Kernel.ae_eq_of_compProd_eq
  apply Measure.ext_prod
  intro A B hA hB
  rw [Measure.compProd_apply_prod hA hB, Measure.compProd_apply_prod hA hB]
  exact lintegral_congr_ae (ae_restrict_of_ae (he B hB))

end ProbabilityTheory
