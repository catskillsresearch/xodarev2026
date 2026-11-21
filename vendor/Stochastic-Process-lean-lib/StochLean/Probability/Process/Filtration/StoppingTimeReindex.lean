/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import Mathlib.Probability.Process.Stopping

/-! # Reindexing a filtration by an ordered family of stopping times -/

@[expose] public section

open scoped NNReal

namespace MeasureTheory

variable {Ω ι : Type*} {mΩ : MeasurableSpace Ω} [Preorder ι]

/-- The sampled filtration consists of the canonical stopping-time sigma-algebras.
Its construction does not assume that the stopping times are finite or bounded. -/
def Filtration.stoppingTimeReindex (F : Filtration ℝ≥0 mΩ)
    (τ : ι → Ω → WithTop ℝ≥0) (hτ : ∀ i, IsStoppingTime F (τ i)) (hmono : Monotone τ) :
    Filtration ι mΩ :=
  ⟨fun i ↦ (hτ i).measurableSpace,
    fun _ _ hij ↦ (hτ _).measurableSpace_mono (hτ _) (hmono hij),
    fun i ↦ (hτ i).measurableSpace_le⟩

@[simp] theorem Filtration.stoppingTimeReindex_apply (F : Filtration ℝ≥0 mΩ)
    (τ : ι → Ω → WithTop ℝ≥0) (hτ : ∀ i, IsStoppingTime F (τ i)) (hmono : Monotone τ)
    (i : ι) : F.stoppingTimeReindex τ hτ hmono i = (hτ i).measurableSpace := rfl

end MeasureTheory
