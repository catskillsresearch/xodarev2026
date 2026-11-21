/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Martingale.Inequalities.OneSidedWeakFiniteTime
public import StochLean.ForMathlib.MeasureTheory.WeakBoundFinite

/-! # Locally bounded countable skeletons before path regularization

Finite-prefix estimates pass to arbitrary bounded deterministic sample sequences.
The resulting weak bound proves almost-sure finiteness, without assuming regular
paths. Countably many integer horizons give one event of local boundedness.
This does not yet bound every real-time value of an unregularized process.
-/

@[expose] public section

open Finset Filter Set
open scoped NNReal ENNReal

namespace MeasureTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsFiniteMeasure P]
  {F : Filtration ℝ≥0 mΩ} {X : ℝ≥0 → Ω → ℝ} {T : ℝ≥0}

theorem Supermartingale.measure_exists_norm_sample_gt_le (hX : Supermartingale X F P)
    (e : ℕ → ℝ≥0) (he : ∀ n, e n ≤ T) (ε : ℝ≥0) :
    (ε : ℝ≥0∞) * P {ω | ∃ n, (ε : ℝ) < ‖X (e n) ω‖} ≤
      ENNReal.ofReal ((∫ ω, X 0 ω ∂P) + 2 * (∫ ω, ‖X T ω‖ ∂P)) := by
  classical
  let A (n : ℕ) := {ω | ∃ k ≤ n, (ε : ℝ) < ‖X (e k) ω‖}
  have hm : Monotone A := by
    rintro i j hij ω ⟨k, hki, hk⟩
    exact ⟨k, hki.trans hij, hk⟩
  have hb (n : ℕ) : (ε : ℝ≥0∞) * P (A n) ≤
      ENNReal.ofReal ((∫ ω, X 0 ω ∂P) + 2 * (∫ ω, ‖X T ω‖ ∂P)) := by
    let s := (range (n + 1)).image e
    have hs : s.Nonempty := nonempty_range_add_one.image _
    apply le_trans _ (hX.measure_norm_finset_sup_le s hs (by
      rintro t ht
      obtain ⟨k, _, rfl⟩ := mem_image.mp ht
      exact he k) ε)
    apply mul_le_mul le_rfl _ bot_le bot_le
    apply measure_mono
    rintro ω ⟨k, hkn, hk⟩
    exact hk.le.trans (le_sup' (fun t ↦ ‖X t ω‖)
      (mem_image.mpr ⟨k, mem_range.mpr (Nat.lt_succ_of_le hkn), rfl⟩))
  have heq : {ω | ∃ n, (ε : ℝ) < ‖X (e n) ω‖} = ⋃ n, A n := by
    ext ω
    simp only [mem_ofPred_eq, mem_iUnion, A]
    exact ⟨fun ⟨n, hn⟩ ↦ ⟨n, n, le_rfl, hn⟩, fun ⟨_, n, _, hn⟩ ↦ ⟨n, hn⟩⟩
  rw [heq, hm.measure_iUnion, ENNReal.mul_iSup]
  exact iSup_le hb

theorem Supermartingale.ae_bddAbove_norm_sample (hX : Supermartingale X F P)
    (e : ℕ → ℝ≥0) (he : ∀ n, e n ≤ T) :
    ∀ᵐ ω ∂P, BddAbove (Set.range fun n ↦ ‖X (e n) ω‖) := by
  let Z (ω) : ℝ≥0∞ := ⨆ n, ENNReal.ofReal ‖X (e n) ω‖
  have hf : ∀ᵐ ω ∂P, Z ω < ⊤ := by
    apply ae_lt_top_of_nat_mul_measure_gt_le
      (C := ENNReal.ofReal ((∫ ω, X 0 ω ∂P) + 2 * (∫ ω, ‖X T ω‖ ∂P)))
      ENNReal.ofReal_ne_top
    intro n
    have heq : {ω | (n : ℝ≥0∞) < Z ω} = {ω | ∃ k, (n : ℝ) < ‖X (e k) ω‖} := by
      ext ω
      simp only [mem_ofPred_eq, Z, lt_iSup_iff]
      apply exists_congr
      intro k
      rw [← ENNReal.ofReal_natCast,
        ENNReal.ofReal_lt_ofReal_iff_of_nonneg (Nat.cast_nonneg n)]
    rw [heq]
    simpa only [ENNReal.coe_natCast, NNReal.coe_natCast] using
      hX.measure_exists_norm_sample_gt_le e he (n : ℝ≥0)
  filter_upwards [hf] with ω hω
  refine ⟨(Z ω).toReal, ?_⟩
  rintro _ ⟨n, rfl⟩
  apply (ENNReal.ofReal_le_iff_le_toReal hω.ne).mp
  exact le_iSup (fun n ↦ ENNReal.ofReal ‖X (e n) ω‖) n

theorem Supermartingale.ae_locally_bddAbove_norm_sample (hX : Supermartingale X F P)
    (e : ℕ → ℝ≥0) :
    ∀ᵐ ω ∂P, ∀ T : ℝ≥0, ∃ C : ℝ, ∀ n, e n ≤ T → ‖X (e n) ω‖ ≤ C := by
  have h (N : ℕ) := hX.ae_bddAbove_norm_sample (T := (N : ℝ≥0))
    (fun n ↦ min (e n) N) (fun _ ↦ min_le_right _ _)
  have ha := ae_all_iff.mpr h
  filter_upwards [ha] with ω hω T
  obtain ⟨N, hN⟩ := exists_nat_ge T
  obtain ⟨C, hC⟩ := hω N
  refine ⟨C, fun n hn ↦ ?_⟩
  have hb := hC (Set.mem_range_self n)
  simpa only [min_eq_left (hn.trans hN)] using hb

theorem Submartingale.measure_exists_norm_sample_gt_le (hX : Submartingale X F P)
    (e : ℕ → ℝ≥0) (he : ∀ n, e n ≤ T) (ε : ℝ≥0) :
    (ε : ℝ≥0∞) * P {ω | ∃ n, (ε : ℝ) < ‖X (e n) ω‖} ≤
      ENNReal.ofReal (-(∫ ω, X 0 ω ∂P) + 2 * (∫ ω, ‖X T ω‖ ∂P)) := by
  simpa only [Pi.neg_apply, norm_neg, integral_neg] using
    hX.neg.measure_exists_norm_sample_gt_le e he ε

theorem Submartingale.ae_bddAbove_norm_sample (hX : Submartingale X F P)
    (e : ℕ → ℝ≥0) (he : ∀ n, e n ≤ T) :
    ∀ᵐ ω ∂P, BddAbove (Set.range fun n ↦ ‖X (e n) ω‖) := by
  simpa only [Pi.neg_apply, norm_neg] using hX.neg.ae_bddAbove_norm_sample e he

theorem Submartingale.ae_locally_bddAbove_norm_sample (hX : Submartingale X F P)
    (e : ℕ → ℝ≥0) :
    ∀ᵐ ω ∂P, ∀ T : ℝ≥0, ∃ C : ℝ, ∀ n, e n ≤ T → ‖X (e n) ω‖ ≤ C := by
  simpa only [Pi.neg_apply, norm_neg] using hX.neg.ae_locally_bddAbove_norm_sample e

end MeasureTheory
