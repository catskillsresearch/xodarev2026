/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Martingale.Inequalities.DoobFiniteTime
public import StochLean.Probability.Process.Filtration.SubmartingaleReindex

/-! # Finite-time Doob Lp bounds for nonnegative submartingales

Sorted samples reuse the native natural-time submartingale and the project's
strong maximal inequality. This is the one-sided input needed in Protter I.20.
No terminal Lp-integrability assumption is needed for the extended inequality.
-/

@[expose] public section

open StochLean Finset
open scoped NNReal ENNReal

namespace MeasureTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsFiniteMeasure P]
  {F : Filtration ℝ≥0 mΩ} {X : ℝ≥0 → Ω → ℝ} {T : ℝ≥0} {p : ℝ}

theorem Submartingale.eLpNorm_partitionMax_le (hX : Submartingale X F P)
    (hn : ∀ t ω, 0 ≤ X t ω) (hp : 1 < p) (π : TimePartition T) :
    eLpNorm (fun ω ↦ (range (π.size + 1)).sup' nonempty_range_add_one
      (fun k ↦ X (π.pointNat k) ω)) (ENNReal.ofReal p) P ≤
        ENNReal.ofReal (p / (p - 1)) * eLpNorm (X T) (ENNReal.ofReal p) P := by
  have ht : π.pointNat π.size = T := by
    simpa only [Fin.val_last] using
      (π.pointNat_fin (Fin.last π.size)).trans π.last_eq_horizon
  simpa only [ht] using
    maximal_ineq_Lp (hX.reindex π.pointNat π.pointNat_mono) (fun k ↦ hn _) hp π.size

theorem Submartingale.eLpNorm_finset_sup_le (hX : Submartingale X F P)
    (hn : ∀ t ω, 0 ≤ X t ω) (hp : 1 < p)
    (s : Finset ℝ≥0) (hs : s.Nonempty) (hT : ∀ t ∈ s, t ≤ T) :
    eLpNorm (fun ω ↦ s.sup' hs (fun t ↦ X t ω)) (ENNReal.ofReal p) P ≤
      ENNReal.ofReal (p / (p - 1)) * eLpNorm (X T) (ENNReal.ofReal p) P := by
  classical
  let π : TimePartition T := TimePartition.ofFinset (insert 0 (insert T s))
    (by simp) (by simp) (by
      intro t ht
      simp only [mem_insert] at ht
      rcases ht with rfl | rfl | ht
      · exact bot_le
      · exact le_rfl
      · exact hT t ht)
  apply le_trans _ (hX.eLpNorm_partitionMax_le hn hp π)
  apply eLpNorm_mono
  intro ω
  have hsn : 0 ≤ s.sup' hs (fun t ↦ X t ω) := by
    obtain ⟨t, ht⟩ := hs
    exact (hn t ω).trans (le_sup' (fun t ↦ X t ω) ht)
  have hpn : 0 ≤ (range (π.size + 1)).sup' nonempty_range_add_one
      (fun k ↦ X (π.pointNat k) ω) :=
    (hn (π.pointNat 0) ω).trans (le_sup' (fun k ↦ X (π.pointNat k) ω) (by simp))
  rw [Real.norm_eq_abs, abs_of_nonneg hsn, Real.norm_eq_abs, abs_of_nonneg hpn]
  apply sup'_le
  intro t ht
  obtain ⟨i, hi⟩ : t ∈ Set.range π.point := by
    rw [TimePartition.ofFinset_range]
    simp [ht]
  rw [← hi, ← π.pointNat_fin i]
  exact le_sup' (fun k ↦ X (π.pointNat k) ω) (by simpa only [mem_range] using i.isLt)

end MeasureTheory
