/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import Mathlib.Probability.Kernel.CondDistrib
public import Mathlib.Probability.Kernel.CompProdEqIff

/-! # Conditional distributions agree on an actual history event

If two variables agree almost surely on an event measurable through their
common history, their actual conditional distributions agree on that event
as measures. Restricting the history law restricts the native joint-law
identity to the same event. Finite-kernel uniqueness then gives a single
almost-sure equality of measures, not merely a different exceptional set
for every measurable target set.

Only the target is standard Borel. The sample and history spaces are arbitrary
measurable spaces, the ambient measure need only be finite, and no equality
is claimed at arbitrary history labels outside the actual history event.
The conditional distributions remain Mathlib's original construction.
-/

@[expose] public section

open MeasureTheory Set
open scoped ProbabilityTheory

namespace ProbabilityTheory

/-- Equality of variables on a measurable history event gives equality of
their actual evaluated conditional distributions on one common almost-sure
event. No equality of the variables outside that history event is required. -/
theorem condDistrib_comp_ae_eq_on_history_event
    {Ω K E : Type*} {mΩ : MeasurableSpace Ω} {mK : MeasurableSpace K}
    {mE : MeasurableSpace E} [StandardBorelSpace E] [Nonempty E]
    {P : Measure Ω} [IsFiniteMeasure P]
    {X Y : Ω → E} {H : Ω → K}
    (hX : Measurable X) (hY : Measurable Y) (hH : Measurable H)
    {B : Set K} (hB : MeasurableSet B)
    (hXY : ∀ᵐ ω ∂P, H ω ∈ B → X ω = Y ω) :
    ∀ᵐ ω ∂P, H ω ∈ B → condDistrib X H P (H ω) = condDistrib Y H P (H ω) := by
  have hrect (Z : Ω → E) (hZ : Measurable Z)
      (A : Set K) (C : Set E) (hA : MeasurableSet A) (hC : MeasurableSet C) :
      ((P.map H).restrict B ⊗ₘ condDistrib Z H P) (A ×ˢ C) =
        P ((fun ω ↦ (H ω, Z ω)) ⁻¹' ((A ∩ B) ×ˢ C)) := by
    rw [Measure.compProd_apply_prod hA hC, Measure.restrict_restrict hA,
      ← Measure.compProd_apply_prod (hA.inter hB) hC,
      compProd_map_condDistrib hZ.aemeasurable,
      Measure.map_apply (hH.prodMk hZ) ((hA.inter hB).prod hC)]
  have hjoint : (P.map H).restrict B ⊗ₘ condDistrib X H P =
      (P.map H).restrict B ⊗ₘ condDistrib Y H P := by
    apply Measure.ext_prod
    intro A C hA hC
    rw [hrect X hX A C hA hC, hrect Y hY A C hA hC]
    apply measure_congr
    filter_upwards [hXY] with ω hω
    apply propext
    change (H ω ∈ A ∩ B ∧ X ω ∈ C) ↔ (H ω ∈ A ∩ B ∧ Y ω ∈ C)
    constructor
    · rintro ⟨hAB, hXC⟩
      exact ⟨hAB, hω hAB.2 ▸ hXC⟩
    · rintro ⟨hAB, hYC⟩
      exact ⟨hAB, (hω hAB.2).symm ▸ hYC⟩
  have hκ := Kernel.ae_eq_of_compProd_eq hjoint
  exact ae_of_ae_map hH.aemeasurable (ae_imp_of_ae_restrict hκ)

end ProbabilityTheory
