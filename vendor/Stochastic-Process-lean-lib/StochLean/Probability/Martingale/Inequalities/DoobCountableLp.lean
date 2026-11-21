/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Martingale.Inequalities.DoobNonnegativeFiniteTime
public import StochLean.ForMathlib.MeasureTheory.Function.LpMonotoneSup
public import Mathlib.MeasureTheory.Order.Lattice

/-! # Doob Lp control on any countable deterministic sampling family

No order, escape-to-infinity, or regularity assumption is imposed on the
sampling map. Finite prefixes are sorted before applying Doob's inequality.
The extended countable supremum is not assumed finite.
-/

@[expose] public section

open Finset
open scoped NNReal ENNReal

namespace MeasureTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsFiniteMeasure P]
  {F : Filtration ℝ≥0 mΩ} {X : ℝ≥0 → Ω → ℝ} {p : ℝ}

theorem Submartingale.eLpNorm_iSup_sample_le (hX : Submartingale X F P)
    (hn : ∀ t ω, 0 ≤ X t ω) (hp : 1 < p) (e : ℕ → ℝ≥0) :
    eLpNorm (fun ω ↦ ⨆ n, ENNReal.ofReal (X (e n) ω)) (ENNReal.ofReal p) P ≤
      ENNReal.ofReal (p / (p - 1)) * ⨆ t, eLpNorm (X t) (ENNReal.ofReal p) P := by
  classical
  let s (n : ℕ) := (range (n + 1)).image e
  have hs (n : ℕ) : (s n).Nonempty := nonempty_range_add_one.image _
  let g (n : ℕ) (ω : Ω) := (s n).sup' (hs n) (fun t ↦ X t ω)
  have hgm (n : ℕ) : Measurable (g n) := by
    convert! (Finset.measurable_sup' (hs n) (fun t _ ↦
      (hX.stronglyMeasurable t).measurable.mono (F.le t) le_rfl)) using 1
    ext ω
    simp only [g, Finset.sup'_apply]
  have hgn (n : ℕ) (ω : Ω) : 0 ≤ g n ω := by
    obtain ⟨t, ht⟩ := hs n
    exact (hn t ω).trans (le_sup' (fun t ↦ X t ω) ht)
  have hb (n : ℕ) : eLpNorm (g n) (ENNReal.ofReal p) P ≤
      ENNReal.ofReal (p / (p - 1)) * ⨆ t, eLpNorm (X t) (ENNReal.ofReal p) P := by
    have h := hX.eLpNorm_finset_sup_le hn hp (s n) (hs n)
      (T := (s n).sup' (hs n) id) (fun t ht ↦ le_sup' id ht)
    exact h.trans (mul_le_mul le_rfl (le_iSup (fun t ↦ eLpNorm (X t)
      (ENNReal.ofReal p) P) _) bot_le bot_le)
  have hmono : Monotone (fun n ω ↦ ENNReal.ofReal (g n ω)) := by
    intro i j hij ω
    apply ENNReal.ofReal_le_ofReal
    apply sup'_le
    intro t ht
    exact le_sup' (fun t ↦ X t ω)
      (image_subset_image (range_mono (Nat.add_le_add_right hij 1)) ht)
  have heq (ω : Ω) : (⨆ n, ENNReal.ofReal (g n ω)) =
      ⨆ n, ENNReal.ofReal (X (e n) ω) := by
    apply le_antisymm
    · apply iSup_le
      intro n
      obtain ⟨t, ht, he⟩ := (s n).exists_mem_eq_sup' (hs n) (fun t ↦ X t ω)
      obtain ⟨k, _, rfl⟩ := mem_image.mp ht
      change g n ω = X (e k) ω at he
      rw [he]
      exact le_iSup (fun k ↦ ENNReal.ofReal (X (e k) ω)) k
    · apply iSup_le
      intro k
      apply le_trans _ (le_iSup (fun n ↦ ENNReal.ofReal (g n ω)) k)
      apply ENNReal.ofReal_le_ofReal
      exact le_sup' (fun t ↦ X t ω) (mem_image.mpr ⟨k, by simp, rfl⟩)
  rw [show (fun ω ↦ ⨆ n, ENNReal.ofReal (X (e n) ω)) =
    (fun ω ↦ ⨆ n, ENNReal.ofReal (g n ω)) from funext fun ω ↦ (heq ω).symm]
  rw [eLpNorm_iSup_of_monotone_ennreal
    (f := fun n ω ↦ ENNReal.ofReal (g n ω)) (P := P)
    (fun n ↦ ENNReal.measurable_ofReal.comp (hgm n)) hmono (zero_lt_one.trans hp)]
  apply iSup_le
  intro n
  change eLpNorm (ENNReal.ofReal ∘ g n) (ENNReal.ofReal p) P ≤ _
  rw [eLpNorm_ofReal (g n) (Filter.Eventually.of_forall (hgn n))]
  exact hb n

end MeasureTheory
