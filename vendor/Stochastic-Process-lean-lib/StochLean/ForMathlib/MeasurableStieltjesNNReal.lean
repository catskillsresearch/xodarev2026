/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Analysis.PathVariation.Stieltjes
public import Mathlib.MeasureTheory.Measure.GiryMonad
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Order

/-! # Measurable families of locally finite Stieltjes measures on nonnegative time

Unlike the probability-CDF result on the real line, this result imposes no
normalization or finite total mass. Finite initial-interval restrictions suffice.
-/

@[expose] public section

open Set Filter MeasureTheory
open scoped NNReal ENNReal Topology

namespace StochLean

theorem stieltjesMeasure_Iic_nnreal (f : StieltjesFunction ℝ≥0) (t : ℝ≥0) :
    f.measure (Iic t) = ENNReal.ofReal (f t - f 0) := by
  rw [← Icc_bot, StieltjesFunction.measure_Icc]
  change ENNReal.ofReal (f t - Function.leftLim f 0) = _
  rw [leftLim_eq_of_isBot (show IsBot (0 : ℝ≥0) from fun _ ↦ bot_le)]

theorem measurable_stieltjesMeasure_restrict_Iic_of_measurable_upTo
    {Ω : Type*} [MeasurableSpace Ω] {f : Ω → StieltjesFunction ℝ≥0} (T : ℝ≥0)
    (hf : ∀ t ≤ T, Measurable fun ω ↦ f ω t) :
    Measurable fun ω ↦ (f ω).measure.restrict (Iic T) := by
  let (ω : Ω) : IsFiniteMeasure ((f ω).measure.restrict (Iic T)) :=
    ⟨by rw [Measure.restrict_apply_univ, stieltjesMeasure_Iic_nnreal]; exact ENNReal.ofReal_lt_top⟩
  apply Measurable.measure_of_isPiSystem (μ := fun ω ↦ (f ω).measure.restrict (Iic T))
    (S := range (Iic : ℝ≥0 → Set ℝ≥0))
    ((BorelSpace.measurable_eq (α := ℝ≥0)).trans (borel_eq_generateFrom_Iic ℝ≥0)) isPiSystem_Iic
  · rintro _ ⟨t, rfl⟩
    simp only [Measure.restrict_apply measurableSet_Iic, Iic_inter_Iic,
      stieltjesMeasure_Iic_nnreal]
    exact ENNReal.measurable_ofReal.comp ((hf (min t T) (min_le_right _ _)).sub (hf 0 bot_le))
  · simp only [Measure.restrict_apply_univ, stieltjesMeasure_Iic_nnreal]
    exact ENNReal.measurable_ofReal.comp ((hf T le_rfl).sub (hf 0 bot_le))

theorem measurable_stieltjesMeasure_restrict_Iic {Ω : Type*} [MeasurableSpace Ω]
    {f : Ω → StieltjesFunction ℝ≥0} (hf : ∀ t, Measurable fun ω ↦ f ω t) (T : ℝ≥0) :
    Measurable fun ω ↦ (f ω).measure.restrict (Iic T) :=
  measurable_stieltjesMeasure_restrict_Iic_of_measurable_upTo T (fun t _ ↦ hf t)

theorem measurable_stieltjesMeasure {Ω : Type*} [MeasurableSpace Ω]
    {f : Ω → StieltjesFunction ℝ≥0} (hf : ∀ t, Measurable fun ω ↦ f ω t) :
    Measurable fun ω ↦ (f ω).measure := by
  apply Measure.measurable_of_measurable_coe
  intro s hs
  have hm (n : ℕ) : Measurable fun ω ↦ (f ω).measure (s ∩ Iic (n : ℝ≥0)) := by
    have h := (Measure.measurable_coe hs).comp
      (measurable_stieltjesMeasure_restrict_Iic hf (n : ℝ≥0))
    change Measurable (fun ω ↦ (f ω).measure.restrict (Iic (n : ℝ≥0)) s) at h
    simpa only [Measure.restrict_apply hs] using h
  have hu : (⋃ n : ℕ, s ∩ Iic (n : ℝ≥0)) = s := by
    ext t
    simp only [mem_iUnion, mem_inter_iff, mem_Iic]
    exact ⟨fun ⟨_, ht, _⟩ ↦ ht, fun ht ↦ ⟨Nat.ceil t, ht, Nat.le_ceil t⟩⟩
  apply measurable_of_tendsto_metrizable hm
  apply tendsto_pi_nhds.mpr
  intro ω
  have hmono : Monotone (fun n : ℕ ↦ s ∩ Iic (n : ℝ≥0)) := by
    intro n m hnm
    exact inter_subset_inter_right s (Iic_subset_Iic.mpr (Nat.cast_le.mpr hnm))
  have h := tendsto_measure_iUnion_atTop (μ := (f ω).measure) hmono
  rw [hu] at h
  exact h

end StochLean
