/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.Semimartingale.QuadraticCovariation.ContinuousLeft
public import StochLean.Probability.Process.Semimartingale.QuadraticVariation.ContinuousPartAlgebra

/-! # Orthogonal raw brackets and their continuous components

The common clock may be random. Its initial value is removed for the
continuous bracket. If it starts at zero, every coordinate starts at zero.
-/

@[expose] public section

open MeasureTheory
open scoped NNReal

namespace ProbabilityTheory

theorem continuous_brackets_of_raw_orthogonal_clock_centered
    {ι Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsFiniteMeasure P]
    {F : Filtration ℝ≥0 mΩ} {X : ι → ℝ≥0 → Ω → ℝ} {A : ℝ≥0 → Ω → ℝ}
    (hX : ∀ i, IsSemimartingale (X i) F P) (hF : F.IsUsual P)
    (hc : ∀ i, HasContinuousPaths (X i) P)
    (hd : ∀ i, Indistinguishable ((hX i).quadraticVariation hF) A P)
    (ho : ∀ i j, i ≠ j →
      Indistinguishable ((hX i).quadraticCovariation (hX j) hF) 0 P) :
    (∀ i, Indistinguishable ((hX i).continuousQuadraticVariation hF)
      (fun t ω ↦ A t ω - A 0 ω) P) ∧
      (∀ i j, i ≠ j →
        Indistinguishable ((hX i).continuousQuadraticCovariation (hX j) hF) 0 P) := by
  constructor
  · intro i
    filter_upwards [(hX i).continuousQuadraticVariation_eq_of_continuous hF (hc i),
      hd i, (hX i).quadraticVariation_zero_ae hF] with ω he hdω h0 t
    have hi : (X i 0 ω) ^ 2 = A 0 ω := h0.symm.trans (hdω 0)
    simpa only [hdω t, hi] using he t
  · intro i j hij
    filter_upwards [(hX i).continuousQuadraticCovariation_eq_of_left_continuous
      (hX j) hF (hc i), ho i j hij, (hX i).quadraticCovariation_zero_ae (hX j) hF]
      with ω he hoω h0 t
    have hi : X i 0 ω * X j 0 ω = 0 := h0.symm.trans (hoω 0)
    simpa only [hoω t, hi, Pi.zero_apply, sub_zero] using he t

theorem continuous_brackets_of_raw_orthogonal_clock
    {ι Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsFiniteMeasure P]
    {F : Filtration ℝ≥0 mΩ} {X : ι → ℝ≥0 → Ω → ℝ} {A : ℝ≥0 → Ω → ℝ}
    (hX : ∀ i, IsSemimartingale (X i) F P) (hF : F.IsUsual P)
    (hc : ∀ i, HasContinuousPaths (X i) P) (hA0 : A 0 =ᵐ[P] 0)
    (hd : ∀ i, Indistinguishable ((hX i).quadraticVariation hF) A P)
    (ho : ∀ i j, i ≠ j →
      Indistinguishable ((hX i).quadraticCovariation (hX j) hF) 0 P) :
    (∀ i, Indistinguishable ((hX i).continuousQuadraticVariation hF) A P) ∧
      (∀ i j, i ≠ j →
        Indistinguishable ((hX i).continuousQuadraticCovariation (hX j) hF) 0 P) := by
  have h := continuous_brackets_of_raw_orthogonal_clock_centered hX hF hc hd ho
  refine ⟨fun i ↦ ?_, h.2⟩
  filter_upwards [h.1 i, hA0] with ω he h0 t
  simpa only [h0, Pi.zero_apply, sub_zero] using he t

end ProbabilityTheory
