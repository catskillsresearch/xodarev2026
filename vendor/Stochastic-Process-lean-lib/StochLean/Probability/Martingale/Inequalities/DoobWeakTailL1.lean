/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Martingale.Inequalities.DoobWeakGlobalL1
public import StochLean.Probability.Martingale.Convergence.ContinuousLpContraction

/-! # Weak L1 control of a closed martingale's entire tail

Freezing before the starting time gives a true martingale in a reindexed
filtration. Conditional-expectation contraction bounds every increment by
the closing error. Global weak Doob then controls all later times at once.
-/

@[expose] public section

open ProbabilityTheory Filter Set
open scoped NNReal ENNReal

namespace MeasureTheory.Martingale

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsFiniteMeasure P]
  {F : Filtration ℝ≥0 mΩ} {X : ℝ≥0 → Ω → ℝ} {Z : Ω → ℝ}

theorem measure_exists_tail_increment_gt_le (hX : Martingale X F P)
    (hc : HasRightContinuousPaths X P) (hZ : Integrable Z P)
    (hclose : ∀ t, X t =ᵐ[P] P[Z | F t]) (s ε : ℝ≥0) :
    (ε : ℝ≥0∞) * P {ω | ∃ t, s ≤ t ∧ (ε : ℝ) < ‖X t ω - X s ω‖} ≤
      eLpNorm (X s - Z) 1 P := by
  let e (t : ℝ≥0) := max s t
  have he : Monotone e := fun _ _ h ↦ max_le_max_left s h
  have hec : Continuous e := continuous_const.max continuous_id
  let G := F.reindex e he
  let Y (t : ℝ≥0) (ω : Ω) := X (e t) ω - X s ω
  have hXs : StronglyMeasurable[G 0] (X s) := by
    change StronglyMeasurable[F (max s 0)] (X s)
    rw [max_eq_left (show (0 : ℝ≥0) ≤ s from bot_le)]
    exact hX.stronglyAdapted s
  have hY : Martingale Y G P := (hX.reindex e he).sub
    (martingale_const_fun G P hXs (hX.integrable s))
  have hYc : HasRightContinuousPaths Y P := by
    filter_upwards [hc] with ω hω t
    exact ((hω (e t)).comp hec.continuousWithinAt (fun u hu ↦ he hu)).sub
      continuousWithinAt_const
  have hb (t : ℝ≥0) : eLpNorm (Y t) 1 P ≤ eLpNorm (X s - Z) 1 P :=
    hX.eLpNorm_increment_le_closing_error_of_one_le le_rfl hZ hclose (le_max_left s t)
  apply le_trans _ (hY.measure_exists_norm_gt_le_of_eLpNorm_one_le hYc hb ε)
  apply mul_le_mul le_rfl _ (by positivity) (by positivity)
  apply measure_mono
  rintro ω ⟨t, hst, ht⟩
  exact ⟨t, by simpa only [Y, e, max_eq_right hst] using ht⟩

/-- The closing error controls the probability of any later deviation.
The event uses outer measure; no measurability of an uncountable supremum
is assumed. The level is twice the positive scale used in weak Doob. -/
theorem measure_exists_tail_closing_error_gt_le (hX : Martingale X F P)
    (hc : HasRightContinuousPaths X P) (hZ : Integrable Z P)
    (hclose : ∀ t, X t =ᵐ[P] P[Z | F t]) (s ε : ℝ≥0) :
    (ε : ℝ≥0∞) * P {ω | ∃ t, s ≤ t ∧ 2 * (ε : ℝ) < ‖X t ω - Z ω‖} ≤
      2 * eLpNorm (X s - Z) 1 P := by
  let A := {ω | ∃ t, s ≤ t ∧ (ε : ℝ) < ‖X t ω - X s ω‖}
  let B := {ω | (ε : ℝ) < ‖X s ω - Z ω‖}
  have hB : (ε : ℝ≥0∞) * P B ≤ eLpNorm (X s - Z) 1 P := by
    rw [eLpNorm_one_eq_lintegral_enorm]
    apply le_trans _ (mul_meas_ge_le_lintegral₀
      ((hX.integrable s).sub hZ).aestronglyMeasurable.enorm (ε : ℝ≥0∞))
    apply mul_le_mul le_rfl _ (by positivity) (by positivity)
    apply measure_mono
    intro ω hω
    have h := (ENNReal.ofReal_lt_ofReal_iff_of_nonneg ε.coe_nonneg).mpr hω
    simpa only [mem_ofPred_eq, ENNReal.ofReal_coe_nnreal, ofReal_norm, Pi.sub_apply] using h.le
  have hs : {ω | ∃ t, s ≤ t ∧ 2 * (ε : ℝ) < ‖X t ω - Z ω‖} ⊆ A ∪ B := by
    rintro ω ⟨t, hst, ht⟩
    by_contra hω
    have ha : ‖X t ω - X s ω‖ ≤ (ε : ℝ) := by
      by_contra h
      exact hω (Or.inl ⟨t, hst, lt_of_not_ge h⟩)
    have hb : ‖X s ω - Z ω‖ ≤ (ε : ℝ) := by
      by_contra h
      exact hω (Or.inr (lt_of_not_ge h))
    have hd := dist_triangle (X t ω) (X s ω) (Z ω)
    simp only [dist_eq_norm] at hd
    linarith
  calc
    _ ≤ (ε : ℝ≥0∞) * (P A + P B) :=
      mul_le_mul le_rfl ((measure_mono hs).trans (measure_union_le _ _))
        (by positivity) (by positivity)
    _ = (ε : ℝ≥0∞) * P A + (ε : ℝ≥0∞) * P B := mul_add _ _ _
    _ ≤ eLpNorm (X s - Z) 1 P + eLpNorm (X s - Z) 1 P :=
      add_le_add (hX.measure_exists_tail_increment_gt_le hc hZ hclose s ε) hB
    _ = _ := (two_mul _).symm

end MeasureTheory.Martingale
