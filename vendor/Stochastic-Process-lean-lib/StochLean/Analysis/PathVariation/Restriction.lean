/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Analysis.PathVariation.Stopping
public import StochLean.Analysis.PathVariation.EndpointInvariance
public import StochLean.Analysis.PathVariation.AdmissiblePartition

/-! # Exact transport between finite and infinite partition restrictions

Stopping an enclosing finite restriction repeats its terminal endpoint. Direct restriction
deduplicates that endpoint. Endpoint-set invariance proves exact equality of their sums.
-/

@[expose] public section

open Set
open scoped NNReal

namespace StochLean.LocallyFinitePartition

theorem range_stop_restrict (π : LocallyFinitePartition) {s T : ℝ≥0} (hs : s ≤ T) :
    Set.range ((π.restrict T).stop s hs).point = Set.range (π.restrict s).point := by
  ext x
  constructor
  · rintro ⟨i, rfl⟩
    apply (π.mem_range_restrict s _).mpr
    change min ((π.restrict T).point i) s = s ∨
      min ((π.restrict T).point i) s ∈ π.points ∧ min ((π.restrict T).point i) s ≤ s
    by_cases hi : (π.restrict T).point i ≤ s
    · rw [min_eq_left hi]
      rcases (π.mem_range_restrict T _).mp ⟨i, rfl⟩ with hT | ⟨hp, _⟩
      · exact Or.inl (le_antisymm hi (hs.trans_eq hT.symm))
      · exact Or.inr ⟨hp, hi⟩
    · exact Or.inl (min_eq_right (le_of_not_ge hi))
  · intro hx
    rcases (π.mem_range_restrict s x).mp hx with hxs | ⟨hx, hxs⟩
    · subst x
      refine ⟨Fin.last (π.restrict T).size, ?_⟩
      change min ((π.restrict T).point (Fin.last _)) s = s
      rw [(π.restrict T).last_eq_horizon, min_eq_right hs]
    · obtain ⟨i, hi⟩ := (π.mem_range_restrict T x).mpr (Or.inr ⟨hx, hxs.trans hs⟩)
      exact ⟨i, by change min ((π.restrict T).point i) s = x; rw [hi, min_eq_left hxs]⟩

theorem quadraticVariationSum_restrict_eq_stop (π : LocallyFinitePartition)
    {s T : ℝ≥0} (hs : s ≤ T) (f : ℝ≥0 → ℝ) :
    quadraticVariationSum (π.restrict s) f =
      quadraticVariationSum (π.restrict T) (fun t ↦ f (min t s)) :=
  quadraticVariationSum_eq_of_range_eq (π.range_stop_restrict hs).symm f

theorem covariationSum_restrict_eq_stop (π : LocallyFinitePartition)
    {s T : ℝ≥0} (hs : s ≤ T) (f g : ℝ≥0 → ℝ) :
    covariationSum (π.restrict s) f g =
      covariationSum (π.restrict T) (fun t ↦ f (min t s)) (fun t ↦ g (min t s)) :=
  covariationSum_eq_of_range_eq (π.range_stop_restrict hs).symm f g

end StochLean.LocallyFinitePartition
