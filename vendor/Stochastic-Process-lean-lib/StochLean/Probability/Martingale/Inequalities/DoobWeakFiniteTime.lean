/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Martingale.Inequalities.DoobFiniteTime

/-! # Weak L1 Doob bounds on arbitrary finite time sets

Sorting the sampling times reduces the estimate to Mathlib's discrete
maximal inequality. Only true martingality and first moments are used;
no square-integrability or path regularity is required for the finite bound.
-/

@[expose] public section

open StochLean Finset
open scoped NNReal ENNReal

namespace MeasureTheory

variable {Ω E : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsFiniteMeasure P]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {F : Filtration ℝ≥0 mΩ} {X : ℝ≥0 → Ω → E} {T : ℝ≥0}

theorem Martingale.maximal_ineq_norm_partition (hX : Martingale X F P)
    (π : TimePartition T) (ε : ℝ≥0) :
    (ε : ℝ≥0∞) * P {ω | (ε : ℝ) ≤ (range (π.size + 1)).sup' nonempty_range_add_one
      (fun k ↦ ‖X (π.pointNat k) ω‖)} ≤ ENNReal.ofReal (∫ ω, ‖X T ω‖ ∂P) := by
  have ht : π.pointNat π.size = T := by
    simpa only [Fin.val_last] using
      (π.pointNat_fin (Fin.last π.size)).trans π.last_eq_horizon
  have hm := (hX.reindex π.pointNat π.pointNat_mono).norm_submartingale
  have h := maximal_ineq hm (fun _ _ ↦ norm_nonneg _) (ε := ε) π.size
  have hs := setIntegral_le_integral
    (s := {ω | (ε : ℝ) ≤ (range (π.size + 1)).sup' nonempty_range_add_one
      (fun k ↦ ‖X (π.pointNat k) ω‖)}) (hX.integrable T).norm
    (Filter.Eventually.of_forall fun _ ↦ norm_nonneg _)
  apply h.trans
  simpa only [ht] using ENNReal.ofReal_le_ofReal hs

theorem Martingale.measure_norm_finset_sup_le (hX : Martingale X F P)
    (s : Finset ℝ≥0) (hs : s.Nonempty) (hT : ∀ t ∈ s, t ≤ T) (ε : ℝ≥0) :
    (ε : ℝ≥0∞) * P {ω | (ε : ℝ) ≤ s.sup' hs (fun t ↦ ‖X t ω‖)} ≤
      ENNReal.ofReal (∫ ω, ‖X T ω‖ ∂P) := by
  classical
  let π : TimePartition T := TimePartition.ofFinset (insert 0 (insert T s))
    (by simp) (by simp) (by
      intro t ht
      simp only [mem_insert] at ht
      rcases ht with rfl | rfl | ht
      · exact bot_le
      · exact le_rfl
      · exact hT t ht)
  have hmax (ω : Ω) : s.sup' hs (fun t ↦ ‖X t ω‖) ≤
      (range (π.size + 1)).sup' nonempty_range_add_one (fun k ↦ ‖X (π.pointNat k) ω‖) := by
    apply sup'_le
    intro t ht
    obtain ⟨i, hi⟩ : t ∈ Set.range π.point := by
      rw [TimePartition.ofFinset_range]
      simp [ht]
    rw [← hi, ← π.pointNat_fin i]
    exact le_sup' (fun k ↦ ‖X (π.pointNat k) ω‖) (by simpa only [mem_range] using i.isLt)
  apply le_trans _ (hX.maximal_ineq_norm_partition π ε)
  exact mul_le_mul le_rfl (measure_mono fun ω hω ↦ hω.trans (hmax ω))
    (by positivity) (by positivity)

end MeasureTheory
