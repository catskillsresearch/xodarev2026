/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Martingale.Doob.SingleJumpContinuousVersion
public import StochLean.Probability.Process.FiniteVariation.PredictableStieltjesDuality
public import StochLean.Analysis.PathVariation.StieltjesStep

/-! # Totally inaccessible times avoid predictable sets with countable fibers

The actual unit-jump process has a continuous increasing compensating partner
by the already established totally inaccessible Doob construction. Predictable
Stieltjes duality then makes its actual variation measure vanish on every
predictable set with countable time fibers. At a positive finite lifetime this
measure is exactly the unit Dirac mass, yielding the avoidance conclusion.

The infinite lifetime and activation at zero have zero increment variation.
They are handled separately, without interpreting an infinite lifetime as a
finite time. No predictable jump enumeration or general compensator theorem
is assumed in this argument.
-/

@[expose] public section

open MeasureTheory StochLean Filter Set
open scoped NNReal ENNReal

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
  {F : Filtration ℝ≥0 mΩ} {τ : Ω → WithTop ℝ≥0}

/-- Totally inaccessible lifetimes almost surely avoid every predictable
set having countable time fibers, at every positive finite lifetime value. -/
theorem IsTotallyInaccessibleStoppingTime.ae_avoids_predictable_countable_set
    (hτ : IsTotallyInaccessibleStoppingTime F τ P) (hF : F.IsUsual P)
    {S : Set (ℝ≥0 × Ω)} (hS : MeasurableSet[F.predictable] S)
    (hcount : ∀ ω, {t | (t, ω) ∈ S}.Countable) :
    ∀ᵐ ω ∂P, ∀ t : ℝ≥0, 0 < t → τ ω = (t : WithTop ℝ≥0) → (t, ω) ∉ S := by
  classical
  let N : ℝ≥0 → Ω → ℝ := fun t ↦
    {ω | τ ω ≤ (t : WithTop ℝ≥0)}.indicator (fun _ ↦ (1 : ℝ))
  have haN : Adapted F N := fun t ↦ measurable_const.indicator (hτ.1 t)
  have hmN (ω : Ω) : Monotone (N · ω) := by
    intro s t hst
    by_cases hs : τ ω ≤ (s : WithTop ℝ≥0)
    · have ht := hs.trans (WithTop.coe_le_coe.mpr hst)
      simp only [N, indicator_apply, mem_ofPred_eq, if_pos hs, if_pos ht, le_refl]
    · simp only [N, indicator_apply, mem_ofPred_eq, if_neg hs]
      split_ifs <;> norm_num
  have hvN (ω : Ω) : LocallyBoundedVariationOn (N · ω) univ :=
    ((hmN ω).monotoneOn univ).locallyBoundedVariationOn
  have hrN (ω : Ω) : IsRightContinuousPath (N · ω) :=
    (isCadlagPath_indicator_lifetime_le τ (fun _ ↦ (1 : ℝ)) ω).1
  have hiN (t : ℝ≥0) : Integrable (N t) P :=
    (integrable_const (1 : ℝ)).indicator (F.le t _ (hτ.1 t))
  have hkfinite (ω : Ω) (t : ℝ≥0) (ht : τ ω = (t : WithTop ℝ≥0)) :
      totalVariationKernel N haN hvN hrN ω = if t = 0 then 0 else Measure.dirac t := by
    have hv : LocallyBoundedVariationOn
        (fun u : ℝ≥0 ↦ if t ≤ u then (1 : ℝ) else 0) univ := by
      simpa only [N, indicator_apply, mem_ofPred_eq, ht, WithTop.coe_le_coe] using hvN ω
    have hr : IsRightContinuousPath (fun u : ℝ≥0 ↦ if t ≤ u then (1 : ℝ) else 0) := by
      simpa only [N, indicator_apply, mem_ofPred_eq, ht, WithTop.coe_le_coe] using hrN ω
    change (totalVariationStieltjes (N · ω) (hvN ω) (hrN ω)).measure = _
    simpa only [N, indicator_apply, mem_ofPred_eq, ht, WithTop.coe_le_coe] using
      totalVariationStieltjes_measure_step_Ici t hv hr
  have hmass (ω : Ω) : totalVariationKernel N haN hvN hrN ω univ ≤ 1 := by
    cases ht : τ ω with
    | top =>
      have hz : eVariationOn (N · ω) univ = 0 := by
        apply (eVariationOn.eq_zero_iff _).mpr
        intro s _ t _
        simp only [N, indicator_apply, mem_ofPred_eq, ht, WithTop.not_top_le_coe,
          if_false, edist_self]
      rw [totalVariationKernel_univ, hz]
      exact zero_le
    | coe t =>
      rw [hkfinite ω t ht]
      split_ifs <;> simp
  have hvint : HasIntegrableVariation N P := by
    have hm : Measurable (fun ω ↦ eVariationOn (N · ω) univ) := by
      simpa only [totalVariationKernel_univ] using
        (totalVariationKernel N haN hvN hrN).measurable_coe MeasurableSet.univ
    apply (hasIntegrableVariation_iff_lintegral_lt_top hm.aemeasurable).mpr
    calc
      (∫⁻ ω, eVariationOn (N · ω) univ ∂P) ≤ ∫⁻ _ : Ω, (1 : ℝ≥0∞) ∂P := by
        apply lintegral_mono
        intro ω
        simpa only [totalVariationKernel_univ] using hmass ω
      _ < ∞ := by simp
  obtain ⟨B, haB, hcB, hmB, _, hiB, hNB⟩ :=
    hτ.exists_continuous_monotone_compensator_one hF
  have hvB (ω : Ω) : LocallyBoundedVariationOn (B · ω) univ :=
    ((hmB ω).monotoneOn univ).locallyBoundedVariationOn
  have hrB (ω : Ω) : IsRightContinuousPath (B · ω) :=
    fun _ ↦ (hcB ω).continuousWithinAt
  have hzero := ae_totalVariationKernel_eq_zero_of_predictable_countable
    haN hvN hrN hmN haB hvB hrB hmB hcB hiN hiB hvint hNB hS hcount
  filter_upwards [hzero] with ω hω t ht hτt hmem
  rw [hkfinite ω t hτt, if_neg ht.ne',
    Measure.dirac_apply_of_mem (show t ∈ {u | (u, ω) ∈ S} from hmem)] at hω
  exact one_ne_zero hω

end ProbabilityTheory
