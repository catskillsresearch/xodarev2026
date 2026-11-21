/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.UCP.DeviationEvents

/-! # Linear operations and indistinguishable changes in UCP

These statements use the canonical UCP owner and outer-measure event bounds.
No additional path measurability or regularity assumptions are necessary.
-/

@[expose] public section

open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology

namespace ProbabilityTheory

variable {Ω ι : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {l : Filter ι}
  {X Z : ι → ℝ≥0 → Ω → ℝ} {Y W : ℝ≥0 → Ω → ℝ}

theorem TendstoUCP.congr_left (h : TendstoUCP P X l Y)
    (hXZ : ∀ i, Indistinguishable (X i) (Z i) P) : TendstoUCP P Z l Y := by
  intro T ε hε
  have heq : (fun i ↦ P {ω | ε ≤ compactDeviation (X i) Y T ω}) =
      fun i ↦ P {ω | ε ≤ compactDeviation (Z i) Y T ω} := by
    funext i
    apply measure_congr
    filter_upwards [hXZ i] with ω hω
    change (ε ≤ compactDeviation (X i) Y T ω) = (ε ≤ compactDeviation (Z i) Y T ω)
    simp only [compactDeviation, hω]
  rw [← heq]
  exact h T ε hε

theorem TendstoUCP.congr_right (h : TendstoUCP P X l Y)
    (hYW : Indistinguishable Y W P) : TendstoUCP P X l W := by
  intro T ε hε
  have heq : (fun i ↦ P {ω | ε ≤ compactDeviation (X i) Y T ω}) =
      fun i ↦ P {ω | ε ≤ compactDeviation (X i) W T ω} := by
    funext i
    apply measure_congr
    filter_upwards [hYW] with ω hω
    change (ε ≤ compactDeviation (X i) Y T ω) = (ε ≤ compactDeviation (X i) W T ω)
    simp only [compactDeviation, hω]
  rw [← heq]
  exact h T ε hε

theorem TendstoUCP.neg (h : TendstoUCP P X l Y) :
    TendstoUCP P (fun i ↦ -X i) l (-Y) := by
  apply tendstoUCP_iff_measure_exists_norm_lt.mpr
  intro T ε hε
  simpa only [Pi.neg_apply, neg_sub_neg, norm_sub_rev] using
    tendstoUCP_iff_measure_exists_norm_lt.mp h T ε hε

theorem TendstoUCP.add (hX : TendstoUCP P X l Y) (hZ : TendstoUCP P Z l W) :
    TendstoUCP P (fun i ↦ X i + Z i) l (Y + W) := by
  apply tendstoUCP_iff_measure_exists_norm_lt.mpr
  intro T ε hε
  have hsum := (tendstoUCP_iff_measure_exists_norm_lt.mp hX T (ε / 2) (half_pos hε)).add
    (tendstoUCP_iff_measure_exists_norm_lt.mp hZ T (ε / 2) (half_pos hε))
  rw [zero_add] at hsum
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hsum (fun _ ↦ bot_le)
  intro i
  apply (measure_mono (t := {ω | ∃ t ≤ T, ε / 2 < ‖X i t ω - Y t ω‖} ∪
    {ω | ∃ t ≤ T, ε / 2 < ‖Z i t ω - W t ω‖}) ?_).trans (measure_union_le _ _)
  rintro ω ⟨t, ht, hω⟩
  by_cases hXY : ε / 2 < ‖X i t ω - Y t ω‖
  · exact Or.inl ⟨t, ht, hXY⟩
  · refine Or.inr ⟨t, ht, ?_⟩
    change ε < ‖X i t ω + Z i t ω - (Y t ω + W t ω)‖ at hω
    rw [show X i t ω + Z i t ω - (Y t ω + W t ω) =
      (X i t ω - Y t ω) + (Z i t ω - W t ω) by ring] at hω
    have hb := norm_add_le (X i t ω - Y t ω) (Z i t ω - W t ω)
    have hXY := le_of_not_gt hXY
    linarith

theorem TendstoUCP.sub (hX : TendstoUCP P X l Y) (hZ : TendstoUCP P Z l W) :
    TendstoUCP P (fun i ↦ X i - Z i) l (Y - W) := by
  simpa only [sub_eq_add_neg] using hX.add hZ.neg

theorem TendstoUCP.smul (h : TendstoUCP P X l Y) (c : ℝ) :
    TendstoUCP P (fun i ↦ c • X i) l (c • Y) := by
  apply tendstoUCP_iff_measure_exists_norm_lt.mpr
  intro T ε hε
  have hd : 0 < ε / (‖c‖ + 1) := div_pos hε (by positivity)
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
    (tendstoUCP_iff_measure_exists_norm_lt.mp h T _ hd) (fun _ ↦ bot_le)
  intro i
  apply measure_mono
  rintro ω ⟨t, ht, hω⟩
  refine ⟨t, ht, ?_⟩
  change ε < ‖c • X i t ω - c • Y t ω‖ at hω
  rw [← smul_sub, norm_smul] at hω
  by_contra hn
  have hn := le_of_not_gt hn
  have hb := mul_le_mul_of_nonneg_left hn (norm_nonneg c)
  have heq : ε / (‖c‖ + 1) * (‖c‖ + 1) = ε := div_mul_cancel₀ ε (by positivity)
  nlinarith

end ProbabilityTheory
