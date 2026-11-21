/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Martingale.Inequalities.UpcrossingFiniteTime
public import StochLean.Analysis.PathVariation.DenseUpcrossings

/-! # Dense upcrossings on the entire nonnegative time axis

The count is the supremum of the native finite counts on the existing
expanding dyadic partitions. First-moment bounds give a finite expectation
and almost-sure finiteness, simultaneously for all rational level pairs.
No path regularity or uniform integrability is required for these estimates.
-/

@[expose] public section

open MeasureTheory Filter
open scoped NNReal ENNReal

namespace MeasureTheory.Submartingale

open StochLean

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsFiniteMeasure P]
  {F : Filtration ℝ≥0 mΩ} {X : ℝ≥0 → Ω → ℝ} {a b C : ℝ}

omit [IsFiniteMeasure P] in
theorem measurable_denseUpcrossings (hX : Submartingale X F P) (hab : a < b) :
    Measurable (denseUpcrossings a b X) := by
  apply Measurable.iSup
  intro n
  exact measurable_from_top.comp
    (hX.measurable_upcrossings_partition hab (TimePartition.expandingDyadic n))

theorem lintegral_denseUpcrossings_le (hX : Submartingale X F P) (hab : a < b)
    (hC : ∀ t, (∫ ω, ‖X t ω‖ ∂P) ≤ C) :
    (∫⁻ ω, denseUpcrossings a b X ω ∂P) ≤
      ENNReal.ofReal ((C + P.real Set.univ * |a|) / (b - a)) := by
  unfold denseUpcrossings
  rw [lintegral_iSup]
  · apply iSup_le
    intro n
    let π := TimePartition.expandingDyadic n
    have hb := (hX.mul_integral_upcrossings_partition_le_firstMoment a b π).trans
      (add_le_add (hC (n : ℝ≥0)) le_rfl)
    have hi := hX.integrable_upcrossings_partition hab π
    have hn : 0 ≤ᵐ[P] (fun ω ↦
        (upcrossingsBefore a b (fun k ↦ X (π.pointNat k)) (π.size + 1) ω : ℝ)) :=
      Eventually.of_forall fun _ ↦ Nat.cast_nonneg _
    have he := ofReal_integral_eq_lintegral_ofReal hi hn
    simp only [ENNReal.ofReal_natCast] at he
    rw [← he]
    apply ENNReal.ofReal_le_ofReal
    exact (le_div_iff₀ (sub_pos.mpr hab)).mpr (by simpa only [mul_comm] using hb)
  · intro n
    exact measurable_from_top.comp
      (hX.measurable_upcrossings_partition hab (TimePartition.expandingDyadic n))
  · intro i j hij ω
    exact Nat.cast_le.mpr (monotone_upcrossings_expandingDyadic hab ω hij)

theorem ae_denseUpcrossings_lt_top (hX : Submartingale X F P) (hab : a < b)
    (hC : ∀ t, (∫ ω, ‖X t ω‖ ∂P) ≤ C) :
    ∀ᵐ ω ∂P, denseUpcrossings a b X ω < ⊤ :=
  ae_lt_top (hX.measurable_denseUpcrossings hab)
    (ne_top_of_le_ne_top ENNReal.ofReal_ne_top (hX.lintegral_denseUpcrossings_le hab hC))

/-- One common full-measure event, not an uncountable intersection. -/
theorem ae_all_rat_denseUpcrossings_lt_top (hX : Submartingale X F P)
    (hC : ∀ t, (∫ ω, ‖X t ω‖ ∂P) ≤ C) :
    ∀ᵐ ω ∂P, ∀ a b : ℚ, a < b → denseUpcrossings a b X ω < ⊤ := by
  simp only [ae_all_iff]
  intro a b hab
  exact hX.ae_denseUpcrossings_lt_top (Rat.cast_lt.mpr hab) hC

end MeasureTheory.Submartingale
