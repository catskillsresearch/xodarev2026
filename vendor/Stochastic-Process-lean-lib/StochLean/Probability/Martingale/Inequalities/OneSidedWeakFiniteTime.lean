/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Martingale.Inequalities.OneSidedWeakDiscrete
public import StochLean.Probability.Process.Filtration.SubmartingaleReindex
public import StochLean.Analysis.PathVariation.Approximation
public import StochLean.Analysis.PathVariation.AdmissiblePartition

/-! # Signed weak maximal bounds on arbitrary finite time sets

Sorting and adjoining both endpoints transfers the discrete estimate. Repeated
partition endpoints are allowed, and no continuous-time path regularity is used.
-/

@[expose] public section

open StochLean Finset
open scoped NNReal ENNReal

namespace MeasureTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsFiniteMeasure P]
  {F : Filtration ℝ≥0 mΩ} {X : ℝ≥0 → Ω → ℝ} {T : ℝ≥0}

theorem Supermartingale.maximal_ineq_norm_partition (hX : Supermartingale X F P)
    (π : TimePartition T) (ε : ℝ≥0) :
    (ε : ℝ≥0∞) * P {ω | (ε : ℝ) ≤ (range (π.size + 1)).sup' nonempty_range_add_one
      (fun k ↦ ‖X (π.pointNat k) ω‖)} ≤
      ENNReal.ofReal ((∫ ω, X 0 ω ∂P) + 2 * (∫ ω, ‖X T ω‖ ∂P)) := by
  have ht : π.pointNat π.size = T := by
    simpa only [Fin.val_last] using
      (π.pointNat_fin (Fin.last π.size)).trans π.last_eq_horizon
  have hz : π.pointNat 0 = 0 := by
    simpa only [Fin.val_zero] using (π.pointNat_fin 0).trans π.first_eq_zero
  simpa only [ht, hz] using
    (hX.reindex π.pointNat π.pointNat_mono).maximal_ineq_norm_discrete π.size ε

theorem Supermartingale.measure_norm_finset_sup_le (hX : Supermartingale X F P)
    (s : Finset ℝ≥0) (hs : s.Nonempty) (hT : ∀ t ∈ s, t ≤ T) (ε : ℝ≥0) :
    (ε : ℝ≥0∞) * P {ω | (ε : ℝ) ≤ s.sup' hs (fun t ↦ ‖X t ω‖)} ≤
      ENNReal.ofReal ((∫ ω, X 0 ω ∂P) + 2 * (∫ ω, ‖X T ω‖ ∂P)) := by
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
  exact mul_le_mul le_rfl (measure_mono fun ω hω ↦ hω.trans (hmax ω)) bot_le bot_le

theorem Submartingale.maximal_ineq_norm_partition (hX : Submartingale X F P)
    (π : TimePartition T) (ε : ℝ≥0) :
    (ε : ℝ≥0∞) * P {ω | (ε : ℝ) ≤ (range (π.size + 1)).sup' nonempty_range_add_one
      (fun k ↦ ‖X (π.pointNat k) ω‖)} ≤
      ENNReal.ofReal (-(∫ ω, X 0 ω ∂P) + 2 * (∫ ω, ‖X T ω‖ ∂P)) := by
  simpa only [Pi.neg_apply, norm_neg, integral_neg] using
    hX.neg.maximal_ineq_norm_partition π ε

theorem Submartingale.measure_norm_finset_sup_le (hX : Submartingale X F P)
    (s : Finset ℝ≥0) (hs : s.Nonempty) (hT : ∀ t ∈ s, t ≤ T) (ε : ℝ≥0) :
    (ε : ℝ≥0∞) * P {ω | (ε : ℝ) ≤ s.sup' hs (fun t ↦ ‖X t ω‖)} ≤
      ENNReal.ofReal (-(∫ ω, X 0 ω ∂P) + 2 * (∫ ω, ‖X T ω‖ ∂P)) := by
  simpa only [Pi.neg_apply, norm_neg, integral_neg] using
    hX.neg.measure_norm_finset_sup_le s hs hT ε

end MeasureTheory
