/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Analysis.PathVariation.TotalVariation
public import StochLean.Analysis.PathVariation.CeilingIndex
public import StochLean.ForMathlib.Probability.UpcrossingEmbedding

/-! # Refinement and endpoint invariance of upcrossing counts

The existing ceiling-index projection maps each coarse endpoint to the same
point in the finer partition. It is monotone even when endpoints repeat.
The native discrete count therefore increases under endpoint inclusion,
including when the terminal horizon grows, and depends only on the endpoint
set rather than the chosen monotone enumeration.
-/

@[expose] public section

open MeasureTheory Set
open scoped NNReal

namespace StochLean.TimePartition

variable {Ω : Type*} {T S : ℝ≥0} {π : TimePartition T} {ρ : TimePartition S}
  {a b : ℝ} {X : ℝ≥0 → Ω → ℝ} {ω : Ω}

theorem upcrossingsBefore_le_of_range_subset (hab : a < b)
    (h : Set.range ρ.point ⊆ Set.range π.point) :
    upcrossingsBefore a b (fun n ↦ X (ρ.pointNat n)) (ρ.size + 1) ω ≤
      upcrossingsBefore a b (fun n ↦ X (π.pointNat n)) (π.size + 1) ω := by
  let e (n : ℕ) : ℕ := (π.ceilingIndex (ρ.pointNat n)).val
  have he : Monotone e := fun _ _ hij ↦ π.ceilingIndex_mono (ρ.pointNat_mono hij)
  have hb (n : ℕ) (_hn : n < ρ.size + 1) : e n < π.size + 1 :=
    (π.ceilingIndex (ρ.pointNat n)).isLt
  have hsame : (fun n ↦ X (π.pointNat (e n))) = fun n ↦ X (ρ.pointNat n) := by
    funext n
    exact congrArg X (π.pointNat_ceilingIndex_eq_of_mem (h (ρ.pointNat_mem n)))
  simpa only [hsame] using
    (MeasureTheory.upcrossingsBefore_comp_le (f := fun n ↦ X (π.pointNat n)) hab he hb (ω := ω))

theorem Refines.upcrossingsBefore_le {ρ : TimePartition T} (h : π.Refines ρ) (hab : a < b) :
    upcrossingsBefore a b (fun n ↦ X (ρ.pointNat n)) (ρ.size + 1) ω ≤
      upcrossingsBefore a b (fun n ↦ X (π.pointNat n)) (π.size + 1) ω :=
  upcrossingsBefore_le_of_range_subset hab h

theorem upcrossingsBefore_eq_of_range_eq (hab : a < b)
    (h : Set.range π.point = Set.range ρ.point) :
    upcrossingsBefore a b (fun n ↦ X (π.pointNat n)) (π.size + 1) ω =
      upcrossingsBefore a b (fun n ↦ X (ρ.pointNat n)) (ρ.size + 1) ω :=
  le_antisymm (upcrossingsBefore_le_of_range_subset hab h.subset)
    (upcrossingsBefore_le_of_range_subset hab h.symm.subset)

end StochLean.TimePartition
