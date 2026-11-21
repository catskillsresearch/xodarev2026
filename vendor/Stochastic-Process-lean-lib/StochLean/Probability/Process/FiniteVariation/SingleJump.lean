/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.FiniteVariation.Integrable
public import StochLean.Probability.Process.Path.RightStep
public import StochLean.Analysis.PathVariation.CompletedSums
public import Mathlib.MeasureTheory.Constructions.BorelSpace.WithTop
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Integral.IntegrableOn

/-! # Actual integrable variation of a single lifetime step

The closed-step process uses the existing lifetime indicator. Its whole-half-line
extended variation is exactly the norm of its coefficient at a positive finite
lifetime, and zero at zero or infinite lifetime. A zero lifetime gives a constant
path, so its initial value contributes no variation. An infinite lifetime never
activates at a finite time.

The variation formula is pathwise and needs no measurability. A measurable
lifetime and an integrable coefficient then give actual integrable variation
and its expectation bound. Neither a filtration, a stopping-time hypothesis,
finiteness of the measure, nor a zero initial value is required. Finiteness of
the extended variation is proved before using its real conversion.
-/

@[expose] public section

open MeasureTheory Set
open scoped NNReal ENNReal

namespace ProbabilityTheory

private theorem eVariationOn_step_Ici_univ (a : ℝ≥0) (c : ℝ) :
    eVariationOn (fun t : ℝ≥0 ↦ if a ≤ t then c else 0) univ =
      if 0 < a then ENNReal.ofReal ‖c‖ else 0 := by
  classical
  by_cases ha : 0 < a
  · rw [if_pos ha]
    apply le_antisymm
    · have he : StochLean.cumulativeStepSum (fun _ : Unit ↦ a) (fun _ ↦ c) =
          (fun t : ℝ≥0 ↦ if a ≤ t then c else 0) := by
        funext t
        simp only [StochLean.cumulativeStepSum, Fintype.sum_unique]
      have hb := StochLean.eVariationOn_cumulativeStepSum_le (fun _ : Unit ↦ a)
        (fun _ : Unit ↦ c) univ
      rw [he] at hb
      simpa only [Fintype.sum_unique, Real.norm_eq_abs] using hb
    · have h := eVariationOn.edist_le (fun t : ℝ≥0 ↦ if a ≤ t then c else 0)
        (mem_univ a) (mem_univ 0)
      simpa only [le_refl, if_true, not_le.mpr ha, if_false, edist_dist,
        dist_zero_right] using h
  · rw [if_neg ha]
    have hz : a = 0 := le_antisymm (le_of_not_gt ha) bot_le
    subst a
    apply (eVariationOn.eq_zero_iff _).mpr
    intro s _ t _
    simp only [zero_le, if_true, edist_self]

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
  {τ : Ω → WithTop ℝ≥0} {Z : Ω → ℝ}

/-- Exact whole-half-line variation of the actual closed lifetime step.
Zero and infinite lifetimes have zero variation for different reasons. -/
theorem eVariationOn_univ_indicator_lifetime_le (τ : Ω → WithTop ℝ≥0)
    (Z : Ω → ℝ) (ω : Ω) :
    eVariationOn
      (fun t : ℝ≥0 ↦ {ω | τ ω ≤ (t : WithTop ℝ≥0)}.indicator Z ω) univ =
        if 0 < τ ω ∧ τ ω < ⊤ then ENNReal.ofReal ‖Z ω‖ else 0 := by
  classical
  cases ht : τ ω with
  | top =>
    simp only [indicator_apply, mem_ofPred_eq, ht, WithTop.not_top_le_coe,
      if_false, lt_self_iff_false, and_false]
    exact (eVariationOn.eq_zero_iff _).mpr fun _ _ _ _ ↦ edist_self 0
  | coe a =>
    simpa only [indicator_apply, mem_ofPred_eq, ht, WithTop.coe_le_coe,
      WithTop.coe_lt_top, and_true, ← WithTop.coe_zero, WithTop.coe_lt_coe] using
        eVariationOn_step_Ici_univ a (Z ω)

/-- Integrability of the coefficient controls the actual extended variation;
the lifetime need only be measurable, not a stopping time. -/
theorem hasIntegrableVariation_indicator_lifetime_le (hτ : Measurable τ)
    (hZ : Integrable Z P) :
    HasIntegrableVariation
      (fun t : ℝ≥0 ↦ {ω | τ ω ≤ (t : WithTop ℝ≥0)}.indicator Z) P := by
  classical
  have hE : MeasurableSet {ω | 0 < τ ω ∧ τ ω < ⊤} :=
    (measurableSet_lt measurable_const hτ).inter (measurableSet_lt hτ measurable_const)
  constructor
  · exact Filter.Eventually.of_forall fun ω ↦ by
      change eVariationOn
        (fun t : ℝ≥0 ↦ {ω | τ ω ≤ (t : WithTop ℝ≥0)}.indicator Z ω) univ ≠ ∞
      rw [eVariationOn_univ_indicator_lifetime_le]
      split_ifs
      · exact ENNReal.ofReal_ne_top
      · exact ENNReal.zero_ne_top
  · have he : (fun ω ↦ (eVariationOn
        (fun t : ℝ≥0 ↦ {ω | τ ω ≤ (t : WithTop ℝ≥0)}.indicator Z ω) univ).toReal) =
          {ω | 0 < τ ω ∧ τ ω < ⊤}.indicator (fun ω ↦ ‖Z ω‖) := by
      funext ω
      rw [eVariationOn_univ_indicator_lifetime_le]
      by_cases hω : 0 < τ ω ∧ τ ω < ⊤
      · simp only [ENNReal.toReal_ofReal (norm_nonneg _),
          indicator_apply, mem_ofPred_eq, if_pos hω]
      · simp only [ENNReal.toReal_zero, indicator_apply, mem_ofPred_eq, if_neg hω]
    rw [he]
    exact hZ.norm.indicator hE

/-- Expected actual total variation is bounded by the coefficient's first
absolute moment, without requiring a finite lifetime or a finite measure. -/
theorem integral_eVariationOn_indicator_lifetime_le (hτ : Measurable τ)
    (hZ : Integrable Z P) :
    (∫ ω, (eVariationOn
      (fun t : ℝ≥0 ↦ {ω | τ ω ≤ (t : WithTop ℝ≥0)}.indicator Z ω) univ).toReal ∂P) ≤
        ∫ ω, ‖Z ω‖ ∂P := by
  apply integral_mono
    (hasIntegrableVariation_indicator_lifetime_le hτ hZ).integrable_eVariationOn_toReal
    hZ.norm
  intro ω
  dsimp only
  rw [eVariationOn_univ_indicator_lifetime_le]
  split_ifs
  · exact (ENNReal.toReal_ofReal (norm_nonneg _)).le
  · simpa only [ENNReal.toReal_zero] using norm_nonneg (Z ω)

end ProbabilityTheory
