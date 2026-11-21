/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import Mathlib.Probability.Martingale.Basic

/-! # Deterministic monotone reindexing of filtrations and martingales -/

@[expose] public section

namespace MeasureTheory

variable {Ω ι κ E : Type*} {mΩ : MeasurableSpace Ω} [Preorder ι] [Preorder κ]

def Filtration.reindex (F : Filtration ι mΩ) (e : κ → ι) (he : Monotone e) :
    Filtration κ mΩ :=
  ⟨fun k ↦ F (e k), fun _ _ h ↦ F.mono (he h), fun k ↦ F.le (e k)⟩

@[simp] theorem Filtration.reindex_apply (F : Filtration ι mΩ) (e : κ → ι)
    (he : Monotone e) (k : κ) : F.reindex e he k = F (e k) := rfl

theorem Martingale.reindex [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {F : Filtration ι mΩ} {P : Measure Ω} {X : ι → Ω → E} (hX : Martingale X F P)
    (e : κ → ι) (he : Monotone e) : Martingale (fun k ↦ X (e k)) (F.reindex e he) P :=
  ⟨fun k ↦ hX.stronglyAdapted (e k), fun _ _ h ↦ hX.condExp_ae_eq (he h)⟩

end MeasureTheory
