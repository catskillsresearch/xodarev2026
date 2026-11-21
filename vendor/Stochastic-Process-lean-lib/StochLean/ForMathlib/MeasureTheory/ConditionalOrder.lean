/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic
public import Mathlib.MeasureTheory.Function.AEEqOfIntegral

/-! # Conditional order from set-integral comparisons

The comparison is tested only on the conditioning sigma-field. Passing to
the trimmed measure allows the native set-integral order criterion to apply.
-/

@[expose] public section

namespace MeasureTheory

theorem ae_le_condExp_of_forall_setIntegral_le
    {Ω : Type*} {m mΩ : MeasurableSpace Ω} {P : Measure Ω} (hm : m ≤ mΩ)
    [SigmaFinite (P.trim hm)] {f g : Ω → ℝ} (hf : Integrable f P) (hg : Integrable g P)
    (hfm : StronglyMeasurable[m] f)
    (hle : ∀ A, MeasurableSet[m] A → (∫ ω in A, f ω ∂P) ≤ ∫ ω in A, g ω ∂P) :
    f ≤ᵐ[P] P[g | m] := by
  apply ae_of_ae_trim hm
  apply ae_le_of_forall_setIntegral_le (Integrable.trim hm hf hfm)
    (Integrable.trim hm integrable_condExp stronglyMeasurable_condExp)
  intro A hA _
  rw [← setIntegral_trim hm hfm hA, ← setIntegral_trim hm stronglyMeasurable_condExp hA,
    setIntegral_condExp hm hg hA]
  exact hle A hA

end MeasureTheory
