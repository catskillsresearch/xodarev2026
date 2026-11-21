/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Martingale.Inequalities.DoobWeakFiniteTime
public import StochLean.Probability.Process.Path.Supremum

/-! # Weak L1 maximal control in continuous time

An increasing union of finite exceedance events gives the exact weak bound
for the existing extended dense supremum. Right continuity then transfers it
to an existential exceedance anywhere in the compact interval. No L2 or
real-valued supremum finiteness premise is required.
-/

@[expose] public section

open ProbabilityTheory Filter Finset Set
open scoped NNReal ENNReal

namespace MeasureTheory

variable {Ω E : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsFiniteMeasure P]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {F : Filtration ℝ≥0 mΩ} {X : ℝ≥0 → Ω → E} {T : ℝ≥0}

theorem Martingale.measure_denseRunningSupremum_norm_gt_le (hX : Martingale X F P)
    (T : ℝ≥0) (ε : ℝ≥0) :
    (ε : ℝ≥0∞) * P {ω | (ε : ℝ≥0∞) < denseRunningSupremum (fun t ω ↦ ‖X t ω‖) T ω} ≤
      ENNReal.ofReal (∫ ω, ‖X T ω‖ ∂P) := by
  classical
  let A (n : ℕ) := {ω | ∃ k ≤ n, (ε : ℝ) < ‖X (denseTimeUpTo T k) ω‖}
  have hmono : Monotone A := by
    intro i j hij ω hω
    obtain ⟨k, hki, hk⟩ := hω
    exact ⟨k, hki.trans hij, hk⟩
  have hb (n : ℕ) : (ε : ℝ≥0∞) * P (A n) ≤ ENNReal.ofReal (∫ ω, ‖X T ω‖ ∂P) := by
    let s := (range (n + 1)).image (denseTimeUpTo T)
    have hs : s.Nonempty := nonempty_range_add_one.image _
    apply le_trans _ (hX.measure_norm_finset_sup_le s hs (by
      intro t ht
      obtain ⟨k, _, rfl⟩ := mem_image.mp ht
      exact min_le_left _ _) ε)
    apply mul_le_mul le_rfl _ (by positivity) (by positivity)
    apply measure_mono
    rintro ω ⟨k, hkn, hk⟩
    exact hk.le.trans (le_sup' (fun t ↦ ‖X t ω‖)
      (mem_image.mpr ⟨k, mem_range.mpr (Nat.lt_succ_of_le hkn), rfl⟩))
  have he : {ω | (ε : ℝ≥0∞) < denseRunningSupremum (fun t ω ↦ ‖X t ω‖) T ω} =
      ⋃ n, A n := by
    ext ω
    simp only [mem_ofPred_eq, mem_iUnion, A]
    constructor
    · intro hω
      obtain ⟨k, hk⟩ := lt_iSup_iff.mp hω
      refine ⟨k, k, le_rfl, ?_⟩
      apply (ENNReal.ofReal_lt_ofReal_iff_of_nonneg ε.coe_nonneg).mp
      simpa only [ENNReal.ofReal_coe_nnreal] using hk
    · rintro ⟨n, k, _, hk⟩
      apply lt_iSup_iff.mpr
      refine ⟨k, ?_⟩
      simpa only [ENNReal.ofReal_coe_nnreal] using
        (ENNReal.ofReal_lt_ofReal_iff_of_nonneg ε.coe_nonneg).mpr hk
  rw [he, hmono.measure_iUnion, ENNReal.mul_iSup]
  exact iSup_le hb

/-- The all-times exceedance is bounded using a common right-continuity
event; no uncountable intersection of coordinate null sets is taken. -/
theorem Martingale.measure_exists_norm_gt_le (hX : Martingale X F P)
    (hr : HasRightContinuousPaths X P) (T : ℝ≥0) (ε : ℝ≥0) :
    (ε : ℝ≥0∞) * P {ω | ∃ t ≤ T, (ε : ℝ) < ‖X t ω‖} ≤
      ENNReal.ofReal (∫ ω, ‖X T ω‖ ∂P) := by
  apply le_trans _ (hX.measure_denseRunningSupremum_norm_gt_le T ε)
  apply mul_le_mul le_rfl _ (by positivity) (by positivity)
  apply measure_mono_ae
  filter_upwards [hr] with ω hω ht
  obtain ⟨t, htT, hεt⟩ := ht
  have hlt : (ε : ℝ≥0∞) < ENNReal.ofReal ‖X t ω‖ := by
    simpa only [ENNReal.ofReal_coe_nnreal] using
      (ENNReal.ofReal_lt_ofReal_iff_of_nonneg ε.coe_nonneg).mpr hεt
  exact hlt.trans_le (ofReal_le_denseRunningSupremum_of_rightContinuous htT
    (fun s ↦ (hω s).norm))

end MeasureTheory
