/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import Mathlib.Probability.Kernel.Basic
public import Mathlib.MeasureTheory.Function.Floor
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Real

/-! # S-finiteness from finite kernel fibers

Pointwise finite total masses need not be uniformly bounded. Measurable mass cells
nevertheless decompose such a kernel into uniformly finite kernels. A countable
measurable exhaustion with finite fiber masses gives the same conclusion, after
disjointifying the exhaustion. These results supply genuine `IsSFiniteKernel`
proofs for native kernel integration and measure composition.
-/

@[expose] public section

open Set MeasureTheory
open scoped ENNReal NNReal

namespace ProbabilityTheory.Kernel

variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]

/-- Finite total mass in every fiber suffices for s-finiteness; no uniform mass
bound is needed. The use of `toReal` below is justified by `hκ` in every fiber. -/
theorem isSFiniteKernel_of_finite_fibers (κ : Kernel α β)
    (hκ : ∀ a, κ a univ ≠ ∞) : IsSFiniteKernel κ := by
  classical
  let level (a : α) : ℕ := ⌊(κ a univ).toReal⌋₊
  have hl : Measurable level :=
    (κ.measurable_coe MeasurableSet.univ).ennreal_toReal.nat_floor
  have hm (n : ℕ) : MeasurableSet {a | level a = n} :=
    measurableSet_eq_fun hl measurable_const
  let κs (n : ℕ) : Kernel α β := Kernel.piecewise (hm n) κ 0
  have hκs (n : ℕ) : IsFiniteKernel (κs n) := by
    refine ⟨⟨((n : ℝ≥0∞) + 1), by finiteness, fun a ↦ ?_⟩⟩
    change (if a ∈ {a | level a = n} then κ a else 0) univ ≤ _
    split_ifs with ha
    · have hlevel : level a = n := ha
      have hmass : (κ a univ).toReal ≤ (n : ℝ) + 1 := by
        simpa only [← hlevel] using (Nat.lt_floor_add_one (κ a univ).toReal).le
      rw [← ENNReal.ofReal_toReal (hκ a)]
      exact (ENNReal.ofReal_le_ofReal hmass).trans_eq (by
        rw [ENNReal.ofReal_add (Nat.cast_nonneg n) zero_le_one]
        simp)
    · simp
  refine ⟨⟨κs, hκs, ?_⟩⟩
  ext a s hs
  rw [Kernel.sum_apply' _ _ hs]
  simp only [κs, Kernel.piecewise_apply', mem_ofPred_eq, zero_apply,
    Measure.coe_zero, Pi.zero_apply]
  simp

/-- A countable measurable cover whose sets have finite mass in every fiber
makes the kernel s-finite. No increasing or disjointness premise is required. -/
theorem isSFiniteKernel_of_finite_exhaustion (κ : Kernel α β) (s : ℕ → Set β)
    (hs : ∀ n, MeasurableSet (s n)) (hcover : ⋃ n, s n = univ)
    (hfinite : ∀ a n, κ a (s n) ≠ ∞) : IsSFiniteKernel κ := by
  have hd (n : ℕ) : MeasurableSet (disjointed s n) := MeasurableSet.disjointed hs n
  let κs (n : ℕ) : Kernel α β := κ.restrict (hd n)
  have hκs (n : ℕ) : IsSFiniteKernel (κs n) := by
    apply isSFiniteKernel_of_finite_fibers
    intro a
    change (κ a).restrict (disjointed s n) univ ≠ ∞
    rw [Measure.restrict_apply_univ]
    exact ne_top_of_le_ne_top (hfinite a n) (measure_mono (disjointed_subset s n))
  have heq : κ = Kernel.sum κs := by
    ext1 a
    change κ a = Measure.sum (fun n ↦ (κ a).restrict (disjointed s n))
    rw [← Measure.restrict_iUnion (disjoint_disjointed s) hd,
      iUnion_disjointed, hcover, Measure.restrict_univ]
  rw [heq]
  exact Kernel.isSFiniteKernel_sum_of_denumerable hκs

/-- Local finiteness on all integer initial intervals of the nonnegative time
axis suffices for s-finiteness, even when the whole-halfline mass is infinite. -/
theorem isSFiniteKernel_of_finite_Iic (κ : Kernel α ℝ≥0)
    (hκ : ∀ a (n : ℕ), κ a (Iic (n : ℝ≥0)) ≠ ∞) : IsSFiniteKernel κ := by
  apply isSFiniteKernel_of_finite_exhaustion κ (fun n : ℕ ↦ Iic (n : ℝ≥0))
      (fun _ ↦ measurableSet_Iic)
  · apply eq_univ_of_forall
    intro t
    obtain ⟨n, hn⟩ := exists_nat_ge t
    exact mem_iUnion.mpr ⟨n, hn⟩
  · exact hκ

end ProbabilityTheory.Kernel
