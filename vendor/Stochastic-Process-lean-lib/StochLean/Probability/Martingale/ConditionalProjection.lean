/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import Mathlib.Probability.Martingale.Basic

/-! # Conditional projections of monotone integrable families

Conditioning each member on the current sigma-field turns an increasing
integrable family into a submartingale, or a decreasing family into a
supermartingale. The original family need not be adapted; no optional-projection
owner or sample-path regularity is introduced by these coordinate statements.
-/

@[expose] public section

open Filter

namespace MeasureTheory

variable {ι Ω : Type*} [Preorder ι] {mΩ : MeasurableSpace Ω} {F : Filtration ι mΩ}
  {P : Measure Ω} [IsFiniteMeasure P] {X : ι → Ω → ℝ}

theorem submartingale_condExp_of_ae_monotone
    (hi : ∀ t, Integrable (X t) P) (hm : ∀ s t, s ≤ t → X s ≤ᵐ[P] X t) :
    Submartingale (fun t ↦ P[X t | F t]) F P := by
  refine ⟨fun _ ↦ stronglyMeasurable_condExp, fun s t hst ↦ ?_, fun _ ↦ integrable_condExp⟩
  have hle := condExp_mono (m := F s) (hi s) (hi t) (hm s t hst)
  have he := condExp_condExp_of_le (μ := P) (F.mono hst) (F.le t) (f := X t)
  exact hle.trans_eq he.symm

theorem supermartingale_condExp_of_ae_antitone
    (hi : ∀ t, Integrable (X t) P) (hm : ∀ s t, s ≤ t → X t ≤ᵐ[P] X s) :
    Supermartingale (fun t ↦ P[X t | F t]) F P := by
  refine ⟨fun _ ↦ stronglyMeasurable_condExp, fun s t hst ↦ ?_, fun _ ↦ integrable_condExp⟩
  have hle := condExp_mono (m := F s) (hi t) (hi s) (hm s t hst)
  have he := condExp_condExp_of_le (μ := P) (F.mono hst) (F.le t) (f := X t)
  exact he.trans_le hle

end MeasureTheory
