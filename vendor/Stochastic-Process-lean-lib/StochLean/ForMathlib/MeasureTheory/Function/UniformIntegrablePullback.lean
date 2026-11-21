/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import Mathlib.MeasureTheory.Function.UniformIntegrable

/-! # Uniform integrability under a measure-preserving pullback

The norm-tail criterion transfers through a measure-preserving map because
each norm-tail indicator is itself a pullback and its actual `eLpNorm` is
unchanged. No injectivity, independence, or representation of arbitrary
events on the original sample space is required.
-/

@[expose] public section

open Set
open scoped ENNReal

namespace MeasureTheory

variable {α β E ι : Type*} {mα : MeasurableSpace α} {mβ : MeasurableSpace β}
  [NormedAddCommGroup E] {P : Measure α} {Q : Measure β}
  {φ : α → β} {f : ι → β → E} {p : ℝ≥0∞}

/-- A uniformly integrable family remains uniformly integrable after a
measure-preserving pullback. Only the source measure must be finite. -/
theorem UniformIntegrable.comp_measurePreserving [IsFiniteMeasure P]
    (hf : UniformIntegrable f p Q) (hφ : MeasurePreserving φ P Q)
    (hp : 1 ≤ p) (hpTop : p ≠ ∞) :
    UniformIntegrable (fun i ↦ f i ∘ φ) p P := by
  classical
  refine uniformIntegrable_of hp hpTop
    (fun i ↦ (hf.1 i).comp_measurePreserving hφ) fun ε hε ↦ ?_
  obtain ⟨C, hC⟩ := hf.spec (lt_of_lt_of_le zero_lt_one hp).ne' hpTop hε
  refine ⟨C, fun i ↦ ?_⟩
  have hs : NullMeasurableSet {y | C ≤ ‖f i y‖₊} Q :=
    nullMeasurableSet_le aemeasurable_const (hf.1 i).nnnorm.aemeasurable
  have hm : AEStronglyMeasurable ({y | C ≤ ‖f i y‖₊}.indicator (f i)) Q :=
    (hf.1 i).indicator₀ hs
  have he : {x | C ≤ ‖(f i ∘ φ) x‖₊}.indicator (f i ∘ φ) =
      ({y | C ≤ ‖f i y‖₊}.indicator (f i)) ∘ φ := by
    funext x
    rfl
  rw [he, eLpNorm_comp_measurePreserving hm hφ]
  exact hC i

end MeasureTheory
