/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
public import Mathlib.MeasureTheory.Measure.Real
public import Mathlib.Topology.Algebra.Order.Field

/-! # Finite tail bounds without integrability assumptions

A finite sum is controlled using one positive threshold for all its terms. The denominator
includes one, so empty sums and zero coefficients require no exceptional convention.
All comparisons are almost sure; the exceptional event may vary with the filter index.
-/

@[expose] public section

open Filter Set
open scoped ENNReal Topology

namespace MeasureTheory

variable {Ω ι κ : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsFiniteMeasure P]

theorem measureReal_gt_le_of_ae_le_add_finset_mul (s : Finset ι)
    {W M : Ω → ℝ} {R : ι → Ω → ℝ} {C a : ℝ} (hC : 0 ≤ C) (ha : 0 < a)
    (hW : W ≤ᵐ[P] (fun ω ↦ M ω + C * ∑ i ∈ s, R i ω)) :
    P.real {ω | a < W ω} ≤ P.real {ω | a / 2 < M ω} +
      ∑ i ∈ s, P.real {ω | a / (2 * (C * s.card + 1)) < R i ω} := by
  classical
  let q : ℝ := a / (2 * (C * s.card + 1))
  have hden : 0 < C * (s.card : ℝ) + 1 := by positivity
  have hq : 0 < q := div_pos ha (mul_pos (by norm_num) hden)
  have hmul : (C * (s.card : ℝ) + 1) * q = a / 2 := by
    dsimp [q]
    field_simp
  have hsplit : P {ω | a < W ω} ≤
      P ({ω | a / 2 < M ω} ∪ ⋃ i ∈ s, {ω | q < R i ω}) := by
    apply measure_mono_ae
    filter_upwards [hW] with ω hω hmem
    by_contra hn
    have hm : M ω ≤ a / 2 := by
      exact le_of_not_gt (fun h ↦ hn (Or.inl h))
    have hr : ∀ i ∈ s, R i ω ≤ q := by
      intro i hi
      exact le_of_not_gt (fun h ↦ hn (Or.inr (mem_iUnion.mpr
        ⟨i, mem_iUnion.mpr ⟨hi, h⟩⟩)))
    have hsum : (∑ i ∈ s, R i ω) ≤ (s.card : ℝ) * q := by
      simpa only [Finset.sum_const, nsmul_eq_mul] using Finset.sum_le_sum hr
    have hscale := mul_le_mul_of_nonneg_left hsum hC
    change a < W ω at hmem
    nlinarith
  exact (ENNReal.toReal_mono (measure_ne_top _ _) hsplit).trans
    ((measureReal_union_le _ _).trans (add_le_add le_rfl
      (measureReal_biUnion_finset_le s (fun i ↦ {ω | q < R i ω}))))

theorem TendstoInMeasure.tendsto_measureReal_gt_zero {l : Filter κ} {f : κ → Ω → ℝ}
    (hf : TendstoInMeasure P f l (fun _ ↦ (0 : ℝ))) {a : ℝ} (ha : 0 < a) :
    Tendsto (fun i ↦ P.real {ω | a < f i ω}) l (𝓝 0) := by
  have ht := tendstoInMeasure_iff_measureReal_norm.mp hf a ha
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds ht
    (fun _ ↦ measureReal_nonneg)
  intro i
  apply measureReal_mono (h₂ := measure_ne_top _ _)
  intro ω hω
  change a ≤ ‖f i ω - 0‖
  simpa only [sub_zero, Real.norm_eq_abs] using hω.le.trans (le_abs_self _)

theorem tendstoInMeasure_zero_of_nonneg_of_measureReal_gt {l : Filter κ}
    {f : κ → Ω → ℝ} (hn : ∀ i, 0 ≤ᵐ[P] f i)
    (hprob : ∀ a : ℝ, 0 < a → Tendsto (fun i ↦ P.real {ω | a < f i ω}) l (𝓝 0)) :
    TendstoInMeasure P f l (fun _ ↦ (0 : ℝ)) := by
  apply tendstoInMeasure_iff_measureReal_norm.mpr
  intro a ha
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
    (hprob (a / 2) (half_pos ha)) (fun _ ↦ measureReal_nonneg)
  intro i
  apply ENNReal.toReal_mono (measure_ne_top _ _)
  apply measure_mono_ae
  filter_upwards [hn i] with ω hω hmem
  change a ≤ ‖f i ω - 0‖ at hmem
  have hle : a ≤ f i ω := by simpa only [sub_zero, Real.norm_of_nonneg hω] using hmem
  exact (half_lt_self ha).trans_le hle

end MeasureTheory
