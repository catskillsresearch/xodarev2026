/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import Mathlib.MeasureTheory.Measure.MeasureSpace
public import Mathlib.Data.ENNReal.Operations

/-! # Almost-sure finiteness from weak tail bounds

An extended random quantity with one finite uniform weak bound cannot be
infinite on a positive-measure set. Outer measure suffices; no measurability
or integrability of that quantity is assumed.
-/

@[expose] public section

open scoped ENNReal

namespace MeasureTheory

theorem ae_lt_top_of_nat_mul_measure_gt_le
    {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {f : Ω → ℝ≥0∞}
    {C : ℝ≥0∞} (hC : C ≠ ⊤)
    (hb : ∀ n : ℕ, (n : ℝ≥0∞) * P {ω | (n : ℝ≥0∞) < f ω} ≤ C) :
    ∀ᵐ ω ∂P, f ω < ⊤ := by
  have hs (n : ℕ) : (n : ℝ≥0∞) * P {ω | f ω = ⊤} ≤ C := by
    apply le_trans _ (hb n)
    apply mul_le_mul le_rfl _ bot_le bot_le
    apply measure_mono
    intro ω hω
    simp only [Set.mem_ofPred_eq] at hω ⊢
    rw [hω]
    exact ENNReal.natCast_lt_top n
  have hi : (⊤ : ℝ≥0∞) * P {ω | f ω = ⊤} ≤ C := by
    have hsup := iSup_le hs
    rwa [← ENNReal.iSup_mul, ENNReal.iSup_natCast] at hsup
  have hz : P {ω | f ω = ⊤} = 0 := by
    by_contra hn
    rw [ENNReal.top_mul hn] at hi
    exact hC (top_le_iff.mp hi)
  rw [ae_iff]
  simpa only [lt_top_iff_ne_top, not_not] using hz

end MeasureTheory
