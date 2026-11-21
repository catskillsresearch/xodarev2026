/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import Mathlib.Probability.Martingale.Basic
public import Mathlib.MeasureTheory.Function.ConditionalExpectation.Indicator

/-! # Initial-event masks of submartingales

The event must be measurable in the initial filtration. This is the same
mask used by the existing local-property construction, not arbitrary masking
by a future event.
-/

@[expose] public section

open MeasureTheory Filter Set

namespace MeasureTheory

theorem Submartingale.indicator_initial
    {ι Ω : Type*} [Preorder ι] [OrderBot ι] {mΩ : MeasurableSpace Ω}
    {P : Measure Ω} {F : Filtration ι mΩ} {X : ι → Ω → ℝ}
    (hX : Submartingale X F P) {A : Set Ω} (hA : MeasurableSet[F ⊥] A) :
    Submartingale (fun t ↦ A.indicator (X t)) F P := by
  refine ⟨fun t ↦ (hX.stronglyAdapted t).indicator (F.mono bot_le A hA), ?_,
    fun t ↦ (hX.integrable t).indicator (F.le ⊥ A hA)⟩
  intro s t hst
  filter_upwards [hX.ae_le_condExp hst,
    condExp_indicator (hX.integrable t) (F.mono bot_le A hA)] with ω hω hce
  rw [hce]
  by_cases h : ω ∈ A
  · simpa only [indicator_of_mem h] using hω
  · simp only [indicator_of_notMem h, le_refl]

end MeasureTheory
