/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.ForMathlib.MeasurableStieltjesNNReal

/-! # A nonnegative-time Stieltjes measure is the positive-halfline restriction

If a nonnegative-time Stieltjes function agrees with a real-time Stieltjes
function at every nonnegative time, its measure pushed into the real line
is exactly the real-time measure restricted to strictly positive times.
The native nonnegative-time measure records increments after zero: it has
no initial atom, even when the real-time function jumps at zero. Negative
times are outside the image as well. No probability normalization, global
finiteness, or continuity beyond the Stieltjes structure is assumed.
-/

@[expose] public section

open MeasureTheory Set
open scoped NNReal ENNReal

namespace StieltjesFunction

/-- The actual measure of a compatible nonnegative-time Stieltjes function
maps to the real-time measure with the zero atom and negative halfline removed. -/
theorem measure_map_nnreal_eq_restrict (A : StieltjesFunction ℝ≥0)
    (F : StieltjesFunction ℝ) (h : ∀ t : ℝ≥0, A t = F (t : ℝ)) :
    A.measure.map (fun t : ℝ≥0 ↦ (t : ℝ)) = F.measure.restrict (Ioi (0 : ℝ)) := by
  apply Eq.symm
  refine Measure.ext_of_Ioc' _ _ ?_ ?_
  · intro a b _
    exact ne_top_of_le_ne_top (measure_Ioc_lt_top (μ := F.measure)).ne
      (Measure.restrict_apply_le _ _)
  · intro a b _
    rw [Measure.restrict_apply measurableSet_Ioc,
      Measure.map_apply NNReal.continuous_coe.measurable measurableSet_Ioc]
    by_cases hb : b ≤ 0
    · have he : Ioc a b ∩ Ioi (0 : ℝ) = ∅ := by
        ext x
        simp only [mem_inter_iff, mem_Ioc, mem_Ioi, mem_empty_iff_false, iff_false]
        intro hx
        exact (not_lt_of_ge (hx.1.2.trans hb)) hx.2
      rw [he, measure_empty]
      symm
      apply measure_mono_null ?_ (StochLean.variationStieltjes_measure_zero A)
      intro x hx
      change a < (x : ℝ) ∧ (x : ℝ) ≤ b at hx
      change x = 0
      apply Subtype.ext
      exact le_antisymm (hx.2.trans hb) x.coe_nonneg
    · have hbpos : 0 < b := lt_of_not_ge hb
      let bn : ℝ≥0 := ⟨b, hbpos.le⟩
      by_cases ha : 0 ≤ a
      · let an : ℝ≥0 := ⟨a, ha⟩
        have he : Ioc a b ∩ Ioi (0 : ℝ) = Ioc a b := by
          apply inter_eq_left.mpr
          intro x hx
          exact ha.trans_lt hx.1
        have hp : (fun t : ℝ≥0 ↦ (t : ℝ)) ⁻¹' Ioc a b = Ioc an bn := by
          ext x
          rfl
        rw [he, hp, F.measure_Ioc, A.measure_Ioc, h bn, h an]
        rfl
      · have haneg : a < 0 := lt_of_not_ge ha
        have he : Ioc a b ∩ Ioi (0 : ℝ) = Ioc 0 b := by
          ext x
          simp only [mem_inter_iff, mem_Ioc, mem_Ioi]
          exact ⟨fun hx ↦ ⟨hx.2, hx.1.2⟩,
            fun hx ↦ ⟨⟨haneg.trans hx.1, hx.2⟩, hx.1⟩⟩
        have hp : (fun t : ℝ≥0 ↦ (t : ℝ)) ⁻¹' Ioc a b = Iic bn := by
          ext x
          change (a < (x : ℝ) ∧ (x : ℝ) ≤ b) ↔ (x : ℝ) ≤ b
          exact ⟨fun hx ↦ hx.2, fun hx ↦ ⟨haneg.trans_le x.coe_nonneg, hx⟩⟩
        rw [he, hp, F.measure_Ioc, StochLean.stieltjesMeasure_Iic_nnreal, h bn, h 0]
        rfl

end StieltjesFunction
