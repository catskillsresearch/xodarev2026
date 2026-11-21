/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import Mathlib.Topology.EMetricSpace.BoundedVariation
public import Mathlib.Analysis.Normed.Group.Uniform

/-! # Arithmetic for the canonical bounded-variation predicate -/

@[expose] public section

open Set
open scoped ENNReal

namespace StochLean

variable {α E : Type*} [LinearOrder α] [NormedAddCommGroup E]

theorem eVariationOn_add_le (f g : α → E) (s : Set α) :
    eVariationOn (fun t ↦ f t + g t) s ≤ eVariationOn f s + eVariationOn g s := by
  apply iSup_le
  rintro ⟨n, u, hu, hus⟩
  calc
    _ ≤ ∑ i ∈ Finset.range n, (edist (f (u (i + 1))) (f (u i)) +
        edist (g (u (i + 1))) (g (u i))) :=
      Finset.sum_le_sum fun _ _ ↦ edist_add_add_le _ _ _ _
    _ = (∑ i ∈ Finset.range n, edist (f (u (i + 1))) (f (u i))) +
        ∑ i ∈ Finset.range n, edist (g (u (i + 1))) (g (u i)) := Finset.sum_add_distrib
    _ ≤ _ := add_le_add (eVariationOn.sum_le hu hus) (eVariationOn.sum_le hu hus)

theorem eVariationOn_neg (f : α → E) (s : Set α) :
    eVariationOn (fun t ↦ -f t) s = eVariationOn f s := by
  simp only [eVariationOn, edist_neg_neg]

theorem boundedVariationOn_add {f g : α → E} {s : Set α}
    (hf : BoundedVariationOn f s) (hg : BoundedVariationOn g s) :
    BoundedVariationOn (fun t ↦ f t + g t) s :=
  ne_top_of_le_ne_top (ENNReal.add_ne_top.mpr ⟨hf, hg⟩) (eVariationOn_add_le f g s)

theorem boundedVariationOn_sub {f g : α → E} {s : Set α}
    (hf : BoundedVariationOn f s) (hg : BoundedVariationOn g s) :
    BoundedVariationOn (fun t ↦ f t - g t) s := by
  have hn : BoundedVariationOn (fun t ↦ -g t) s := by
    change eVariationOn (fun t ↦ -g t) s ≠ ∞
    rwa [eVariationOn_neg]
  simpa only [sub_eq_add_neg] using boundedVariationOn_add hf hn

theorem locallyBoundedVariationOn_add {f g : α → E} {s : Set α}
    (hf : LocallyBoundedVariationOn f s) (hg : LocallyBoundedVariationOn g s) :
    LocallyBoundedVariationOn (fun t ↦ f t + g t) s :=
  fun a b ha hb ↦ boundedVariationOn_add (hf a b ha hb) (hg a b ha hb)

theorem locallyBoundedVariationOn_sub {f g : α → E} {s : Set α}
    (hf : LocallyBoundedVariationOn f s) (hg : LocallyBoundedVariationOn g s) :
    LocallyBoundedVariationOn (fun t ↦ f t - g t) s :=
  fun a b ha hb ↦ boundedVariationOn_sub (hf a b ha hb) (hg a b ha hb)

end StochLean
