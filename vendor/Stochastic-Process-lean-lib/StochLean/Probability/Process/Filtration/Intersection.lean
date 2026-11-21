/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.Filtration.Usual
public import Mathlib.Probability.Process.Adapted

/-! # Intersections of usual filtrations

The pointwise intersection retains both right continuity and initial completeness.
A process adapted to both filtrations is adapted to their intersection. No claim
about the right continuity of a generated union of filtrations is needed.
-/

@[expose] public section

open MeasureTheory

namespace MeasureTheory

variable {Ω ι : Type*} {mΩ : MeasurableSpace Ω}

theorem Adapted.inf [Preorder ι] {E : ι → Type*} [∀ i, MeasurableSpace (E i)]
    {F G : Filtration ι mΩ} {H : (i : ι) → Ω → E i}
    (hF : Adapted F H) (hG : Adapted G H) : Adapted (F ⊓ G) H := by
  intro i s hs
  exact ⟨hF i hs, hG i hs⟩

namespace Filtration

variable [LinearOrder ι] [DenselyOrdered ι] [NoMaxOrder ι]
  {F G : Filtration ι mΩ}

theorem IsRightContinuous.inf (hF : F.IsRightContinuous) (hG : G.IsRightContinuous) :
    (F ⊓ G).IsRightContinuous := by
  constructor
  intro i
  change (F ⊓ G).rightCont i ≤ F i ⊓ G i
  refine le_inf ?_ ?_
  · apply le_trans _ (hF.RC i)
    rw [rightCont_eq, rightCont_eq]
    exact iInf_mono fun j ↦ iInf_mono fun _ ↦ inf_le_left
  · apply le_trans _ (hG.RC i)
    rw [rightCont_eq, rightCont_eq]
    exact iInf_mono fun j ↦ iInf_mono fun _ ↦ inf_le_right

theorem IsUsual.inf [OrderBot ι] {P : Measure Ω}
    (hF : F.IsUsual P) (hG : G.IsUsual P) : (F ⊓ G).IsUsual P := by
  refine ⟨hF.1.inf hG.1, ?_⟩
  intro s hs
  exact ⟨hF.2 s hs, hG.2 s hs⟩

end Filtration

end MeasureTheory
