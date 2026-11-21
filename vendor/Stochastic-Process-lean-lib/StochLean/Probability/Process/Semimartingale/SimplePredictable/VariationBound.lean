/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.Semimartingale.SimplePredictable.Normalization
public import StochLean.Analysis.PathVariation.FiniteVariation

/-! # Pathwise variation bounds on elementary integrals

The source time-zero contribution is included separately from increment variation. Real
conversion of extended variation is used only after the corresponding finiteness proof.
-/

@[expose] public section

open MeasureTheory Finset Set
open scoped NNReal ENNReal BigOperators

namespace ProbabilityTheory.SimplePredictableRep

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {F : Filtration ℝ≥0 mΩ}
  {X : ℝ≥0 → Ω → ℝ}

theorem norm_integral_le_variation_of_coefficients (H : SimplePredictableRep F)
    {C : ℝ} (hC : 0 ≤ C) (hi : ∀ ω, ‖H.initial ω‖ ≤ C)
    (hb : ∀ i ω, ‖H.coefficient i ω‖ ≤ C) (ω : Ω)
    (hf : BoundedVariationOn (fun t ↦ X t ω) (Icc 0 (H.partition.terminal ω))) :
    ‖H.integral X ω‖ ≤ C * (‖X 0 ω‖ +
      (eVariationOn (fun t ↦ X t ω) (Icc 0 (H.partition.terminal ω))).toReal) := by
  have hsum : (∑ i : Fin H.partition.size,
      ‖X (H.partition.point i.succ ω) ω - X (H.partition.point i.castSucc ω) ω‖) ≤
      (eVariationOn (fun t ↦ X t ω) (Icc 0 (H.partition.terminal ω))).toReal := by
    exact (H.partition.path ω).sum_abs_increment_le hf
  unfold integral
  calc
    _ ≤ ‖H.initial ω * X 0 ω‖ +
        ‖∑ i, H.coefficient i ω *
          (X (H.partition.point i.succ ω) ω - X (H.partition.point i.castSucc ω) ω)‖ :=
      norm_add_le _ _
    _ ≤ C * ‖X 0 ω‖ + ∑ i : Fin H.partition.size, C *
        ‖X (H.partition.point i.succ ω) ω - X (H.partition.point i.castSucc ω) ω‖ := by
      apply add_le_add
      · rw [norm_mul]
        exact mul_le_mul_of_nonneg_right (hi ω) (norm_nonneg _)
      · apply (norm_sum_le _ _).trans
        apply sum_le_sum
        intro i _
        rw [norm_mul]
        exact mul_le_mul_of_nonneg_right (hb i ω) (norm_nonneg _)
    _ ≤ C * ‖X 0 ω‖ + C *
        (eVariationOn (fun t ↦ X t ω) (Icc 0 (H.partition.terminal ω))).toReal := by
      rw [← mul_sum]
      exact add_le_add (le_refl _) (mul_le_mul_of_nonneg_left hsum hC)
    _ = _ := (mul_add _ _ _).symm

theorem norm_integral_le_variation (H : SimplePredictableRep F) {C : ℝ} (hC : 0 ≤ C)
    (hb : ∀ t ω, ‖H.toProcess t ω‖ ≤ C) (ω : Ω)
    (hf : BoundedVariationOn (fun t ↦ X t ω) (Icc 0 (H.partition.terminal ω))) :
    ‖H.integral X ω‖ ≤ C * (‖X 0 ω‖ +
      (eVariationOn (fun t ↦ X t ω) (Icc 0 (H.partition.terminal ω))).toReal) := by
  rw [← H.integral_removeEmptyIntervals]
  exact H.removeEmptyIntervals.norm_integral_le_variation_of_coefficients hC
    (fun ω ↦ by
      change ‖H.initial ω‖ ≤ C
      simpa only [toProcess_zero] using hb 0 ω)
    (H.norm_coefficient_removeEmptyIntervals_le hC hb) ω hf

theorem norm_integral_le_totalVariation (H : SimplePredictableRep F) {C : ℝ} (hC : 0 ≤ C)
    (hb : ∀ t ω, ‖H.toProcess t ω‖ ≤ C) (ω : Ω)
    (hf : BoundedVariationOn (fun t ↦ X t ω) univ) :
    ‖H.integral X ω‖ ≤ C * (‖X 0 ω‖ + (eVariationOn (fun t ↦ X t ω) univ).toReal) := by
  apply (H.norm_integral_le_variation hC hb ω (hf.mono (subset_univ _))).trans
  exact mul_le_mul_of_nonneg_left
    (add_le_add (le_refl _) (ENNReal.toReal_mono hf (eVariationOn.mono _ (subset_univ _)))) hC

theorem norm_integral_min_const_le_variation (H : SimplePredictableRep F)
    {C : ℝ} (hC : 0 ≤ C) (hb : ∀ t ω, ‖H.toProcess t ω‖ ≤ C) (ω : Ω) (T : ℝ≥0)
    (hf : BoundedVariationOn (fun t ↦ X t ω) (Icc 0 T)) :
    ‖H.integral (fun t ↦ X (min t T)) ω‖ ≤
      C * (‖X 0 ω‖ + (eVariationOn (fun t ↦ X t ω) (Icc 0 T)).toReal) := by
  have hv : eVariationOn (fun t ↦ X (min t T) ω) (Icc 0 (H.partition.terminal ω)) ≤
      eVariationOn (fun t ↦ X t ω) (Icc 0 T) :=
    eVariationOn.comp_le_of_monotoneOn (fun t ↦ X t ω) (fun t ↦ min t T)
      (fun _ _ _ _ h ↦ min_le_min_right _ h) (fun _ _ ↦ ⟨bot_le, min_le_right _ _⟩)
  have hfv : BoundedVariationOn (fun t ↦ X (min t T) ω) (Icc 0 (H.partition.terminal ω)) :=
    ne_top_of_le_ne_top hf hv
  have hi := H.norm_integral_le_variation hC hb ω hfv
  simp only [zero_min] at hi
  exact hi.trans (mul_le_mul_of_nonneg_left (add_le_add (le_refl _) (ENNReal.toReal_mono hf hv)) hC)

end ProbabilityTheory.SimplePredictableRep
