/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.Filtration.Reindex

/-! # Monotone sampling of submartingales and supermartingales

These interfaces reuse the existing filtration reindexing owner and preserve
the direction of the conditional-expectation inequality. They impose neither
strict monotonicity nor path regularity on the sampling map.
-/

@[expose] public section

namespace MeasureTheory

variable {Ω ι κ E : Type*} {mΩ : MeasurableSpace Ω} [Preorder ι] [Preorder κ]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [LE E]
  {F : Filtration ι mΩ} {P : Measure Ω} {X : ι → Ω → E}

theorem Submartingale.reindex (hX : Submartingale X F P) (e : κ → ι) (he : Monotone e) :
    Submartingale (fun k ↦ X (e k)) (F.reindex e he) P :=
  ⟨fun k ↦ hX.1 (e k), fun _ _ h ↦ hX.2.1 _ _ (he h), fun k ↦ hX.2.2 (e k)⟩

theorem Supermartingale.reindex (hX : Supermartingale X F P) (e : κ → ι) (he : Monotone e) :
    Supermartingale (fun k ↦ X (e k)) (F.reindex e he) P :=
  ⟨fun k ↦ hX.1 (e k), fun _ _ h ↦ hX.2.1 _ _ (he h), fun k ↦ hX.2.2 (e k)⟩

end MeasureTheory
