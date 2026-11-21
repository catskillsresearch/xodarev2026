/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import Mathlib.MeasureTheory.Measure.AbsolutelyContinuous
public import Mathlib.MeasureTheory.OuterMeasure.BorelCantelli
public import Mathlib.MeasureTheory.Integral.Indicator
public import Mathlib.Order.Filter.AtTopBot.CountablyGenerated
public import Mathlib.Analysis.SpecificLimits.Basic

/-! # Vanishing event measures under an absolutely continuous finite measure

Events need not be measurable: source-measurable covers of a summable subsequence
permit Borel-Cantelli, and finite target measure gives convergence of their measures.
No continuity of an outer measure on arbitrary nonmeasurable sequences is assumed.
-/

@[expose] public section

open Filter Set
open scoped ENNReal Topology

namespace MeasureTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P Q : Measure Ω} [IsFiniteMeasure Q]

theorem Measure.AbsolutelyContinuous.tendsto_measure_zero {A : ℕ → Set Ω}
    (hQP : Q ≪ P) (hA : Tendsto (fun n ↦ P (A n)) atTop (𝓝 0)) :
    Tendsto (fun n ↦ Q (A n)) atTop (𝓝 0) := by
  apply Filter.tendsto_of_subseq_tendsto
  intro ns hns
  let r : ℕ → ℝ≥0∞ := fun n ↦ (2⁻¹ : ℝ≥0∞) ^ n
  have hrpos : ∀ n, 0 < r n := fun n ↦ ENNReal.pow_pos (by simp) n
  have hrfin : (∑' n, r n) ≠ ∞ := by
    simpa only [r, ENNReal.tsum_geometric, ENNReal.one_sub_inv_two, inv_inv] using
      (ENNReal.ofNat_ne_top : (2 : ℝ≥0∞) ≠ ∞)
  have hsmall : ∀ n, ∃ N, ∀ k ≥ N, P (A (ns k)) ≤ r n := fun n ↦
    ENNReal.tendsto_atTop_zero.mp (hA.comp hns) (r n) (hrpos n)
  choose k hk using hsmall
  let B : ℕ → Set Ω := fun n ↦ toMeasurable P (A (ns (k n)))
  have hB : ∀ n, P (B n) ≤ r n := by
    intro n
    change P (toMeasurable P (A (ns (k n)))) ≤ r n
    rw [measure_toMeasurable]
    exact hk n (k n) le_rfl
  have hsum : (∑' n, P (B n)) ≠ ∞ :=
    ne_top_of_le_ne_top hrfin (ENNReal.tsum_le_tsum hB)
  have hQBae : ∀ᵐ ω ∂Q, ∀ᶠ n in atTop, ω ∉ B n :=
    hQP.ae_le (ae_eventually_notMem hsum)
  have hQB : Tendsto (fun n ↦ Q (B n)) atTop (𝓝 0) := by
    have hh := tendsto_measure_of_ae_tendsto_indicator_of_isFiniteMeasure
      (μ := Q) (As := B) atTop (A := ∅) MeasurableSet.empty
      (fun n ↦ measurableSet_toMeasurable P (A (ns (k n))))
      (hQBae.mono fun ω hω ↦ hω.mono fun n hn ↦
        iff_of_false hn (Set.notMem_empty ω))
    simpa only [measure_empty] using hh
  refine ⟨k, tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hQB
    (fun _ ↦ bot_le) ?_⟩
  intro n
  exact measure_mono (subset_toMeasurable P (A (ns (k n))))

end MeasureTheory
