/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Martingale.OptionalSampling.ContinuousTime
public import StochLean.Probability.Process.LocalMartingale

/-!
# Stopping continuous-time martingales

The bounded optional-sampling theorem is transported to Mathlib's canonical
`WithTop`-valued stopping times. Splitting on the ordering of two stopping times
then gives the minimum formula. In particular a stopped martingale is a
martingale for the original filtration, not merely the stopped filtration.

Source: Protter I.17 and the corollary of I.18. The unrestricted UI conclusion
of I.18 additionally needs the unbounded optional-sampling theorem.
-/

@[expose] public section

open ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology

namespace MeasureTheory.Martingale

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {F : Filtration ℝ≥0 mΩ}
  {P : Measure Ω} {X : ℝ≥0 → Ω → ℝ} [IsFiniteMeasure P] [SigmaFiniteFiltration P F]

theorem stoppedValue_ae_eq_condExp_of_bounded (hX : Martingale X F P)
    (hprog : IsStronglyProgressive F X) (hr : HasRightContinuousPaths X P)
    {τ : Ω → WithTop ℝ≥0} (hτ : IsStoppingTime F τ) {T : ℝ≥0}
    (hbound : ∀ ω, τ ω ≤ T) : stoppedValue X τ =ᵐ[P] P[X T | hτ.measurableSpace] := by
  let hne := fun ω ↦ ne_top_of_le_ne_top WithTop.coe_ne_top (hbound ω)
  let ρ := FiniteStoppingTime.ofNotTop hτ hne
  have hρ : ∀ ω, ρ ω ≤ T := fun ω ↦ WithTop.untopA_le (hbound ω)
  have h := hX.finiteStoppingTime_value_ae_eq_condExp_of_progressive hprog hr ρ hρ
  simpa only [← FiniteStoppingTime.stoppedValue_eq X ρ, ρ,
    FiniteStoppingTime.withTop_ofNotTop, FiniteStoppingTime.measurableSpace_ofNotTop] using h

theorem integrable_stoppedValue_of_bounded (hX : Martingale X F P)
    (hprog : IsStronglyProgressive F X) (hr : HasRightContinuousPaths X P)
    {τ : Ω → WithTop ℝ≥0} (hτ : IsStoppingTime F τ) {T : ℝ≥0}
    (hbound : ∀ ω, τ ω ≤ T) : Integrable (stoppedValue X τ) P :=
  integrable_condExp.congr (hX.stoppedValue_ae_eq_condExp_of_bounded hprog hr hτ hbound).symm

theorem stoppedValue_ae_eq_condExp_of_bounded_le (hX : Martingale X F P)
    (hprog : IsStronglyProgressive F X) (hr : HasRightContinuousPaths X P)
    {σ τ : Ω → WithTop ℝ≥0} (hσ : IsStoppingTime F σ) (hτ : IsStoppingTime F τ)
    (hστ : σ ≤ τ) {T : ℝ≥0} (hbound : ∀ ω, τ ω ≤ T) :
    stoppedValue X σ =ᵐ[P] P[stoppedValue X τ | hσ.measurableSpace] := by
  have hle := hσ.measurableSpace_mono hτ hστ
  have hs := hX.stoppedValue_ae_eq_condExp_of_bounded hprog hr hσ
    (fun ω ↦ (hστ ω).trans (hbound ω))
  have ht := hX.stoppedValue_ae_eq_condExp_of_bounded hprog hr hτ hbound
  exact hs.trans ((condExp_condExp_of_le hle hτ.measurableSpace_le).symm.trans
    (condExp_congr_ae ht).symm)

private theorem condExp_stoppedValue_restrict_le (hX : Martingale X F P)
    (hprog : IsStronglyProgressive F X) (hr : HasRightContinuousPaths X P)
    {σ τ : Ω → WithTop ℝ≥0} (hσ : IsStoppingTime F σ) (hτ : IsStoppingTime F τ)
    {T : ℝ≥0} (hbound : ∀ ω, τ ω ≤ T) :
    P[stoppedValue X τ | hσ.measurableSpace] =ᵐ[P.restrict {ω | τ ω ≤ σ ω}]
      stoppedValue X τ := by
  have hint := hX.integrable_stoppedValue_of_bounded hprog hr hτ hbound
  have hevent := hτ.measurableSet_le_stopping_time hσ
  rw [ae_eq_restrict_iff_indicator_ae_eq (hτ.measurableSpace_le _ hevent)]
  refine (condExp_indicator hint (hτ.measurableSet_stopping_time_le hσ)).symm.trans ?_
  have hi := hint.indicator (hτ.measurableSpace_le _ hevent)
  have hm : StronglyMeasurable[hσ.measurableSpace]
      ({ω | τ ω ≤ σ ω}.indicator (stoppedValue X τ)) := by
    refine StronglyMeasurable.stronglyMeasurable_of_measurableSpace_le_on hevent ?_
      ((measurable_stoppedValue hprog hτ).stronglyMeasurable.indicator hevent) ?_
    · intro A hA
      rw [Set.inter_comm _ A] at hA ⊢
      rw [hτ.measurableSet_inter_le_iff hσ, IsStoppingTime.measurableSet_min_iff hτ hσ] at hA
      exact hA.2
    · intro ω hω
      exact Set.indicator_of_notMem hω _
  exact condExp_of_aestronglyMeasurable' hσ.measurableSpace_le hm.aestronglyMeasurable hi

/-- Bounded-terminal minimum formula; the other stopping time may be infinite. -/
theorem stoppedValue_min_ae_eq_condExp_of_bounded (hX : Martingale X F P)
    (hprog : IsStronglyProgressive F X) (hr : HasRightContinuousPaths X P)
    {σ τ : Ω → WithTop ℝ≥0} (hσ : IsStoppingTime F σ) (hτ : IsStoppingTime F τ)
    {T : ℝ≥0} (hbound : ∀ ω, τ ω ≤ T) :
    stoppedValue X (fun ω ↦ min (σ ω) (τ ω)) =ᵐ[P]
      P[stoppedValue X τ | hσ.measurableSpace] := by
  refine (hX.stoppedValue_ae_eq_condExp_of_bounded_le hprog hr (hσ.min hτ) hτ
    (fun _ ↦ min_le_right _ _) hbound).trans ?_
  refine ae_of_ae_restrict_of_ae_restrict_compl {ω | σ ω ≤ τ ω} ?_ ?_
  · exact condExp_min_stopping_time_ae_eq_restrict_le hσ hτ
  · have heq : P[stoppedValue X τ | (hσ.min hτ).measurableSpace] =ᵐ[
        P.restrict {ω | τ ω ≤ σ ω}] P[stoppedValue X τ | hσ.measurableSpace] := by
      refine (show P[stoppedValue X τ | (hσ.min hτ).measurableSpace] =ᵐ[
        P.restrict {ω | τ ω ≤ σ ω}] P[stoppedValue X τ | hτ.measurableSpace] from ?_).trans ?_
      · rw [hσ.measurableSpace_min hτ, inf_comm, ← hτ.measurableSpace_min hσ]
        exact condExp_min_stopping_time_ae_eq_restrict_le hτ hσ
      · rw [condExp_of_stronglyMeasurable hτ.measurableSpace_le
          (measurable_stoppedValue hprog hτ).stronglyMeasurable
          (hX.integrable_stoppedValue_of_bounded hprog hr hτ hbound)]
        exact (condExp_stoppedValue_restrict_le hX hprog hr hσ hτ hbound).symm
    rw [ae_restrict_iff'
      (hσ.measurableSpace_le _ (hσ.measurableSet_le_stopping_time hτ).compl)]
    rw [Filter.EventuallyEq, ae_restrict_iff'
      (hτ.measurableSpace_le _ (hτ.measurableSet_le_stopping_time hσ))] at heq
    filter_upwards [heq] with ω hω hmem
    exact hω (le_of_not_ge hmem)

/-- Stopping preserves the martingale property for the original filtration. -/
theorem stoppedProcess_of_progressive (hX : Martingale X F P)
    (hprog : IsStronglyProgressive F X) (hr : HasRightContinuousPaths X P)
    {τ : Ω → WithTop ℝ≥0} (hτ : IsStoppingTime F τ) :
    Martingale (stoppedProcess X τ) F P := by
  refine ⟨hprog.stronglyAdapted_stoppedProcess hτ, ?_⟩
  intro s t hst
  have h := hX.stoppedValue_min_ae_eq_condExp_of_bounded hprog hr
    (isStoppingTime_const F s) ((isStoppingTime_const F t).min hτ)
    (fun _ ↦ min_le_left _ _)
  rw [IsStoppingTime.measurableSpace_const] at h
  simpa only [stoppedProcess_eq_stoppedValue, ← min_assoc,
    min_eq_left (WithTop.coe_le_coe.mpr hst)] using h.symm

theorem stoppedProcess_of_rightContinuous (hX : Martingale X F P)
    (hr : ∀ ω, IsRightContinuousPath (X · ω))
    {τ : Ω → WithTop ℝ≥0} (hτ : IsStoppingTime F τ) :
    Martingale (stoppedProcess X τ) F P :=
  hX.stoppedProcess_of_progressive
    (hX.stronglyAdapted.isStronglyProgressive_of_rightContinuous hr) (ae_of_all _ hr) hτ

/-- Bounded stopping of any right-continuous martingale gives a UI martingale. -/
theorem isReducingStoppingTime_of_bounded (hX : Martingale X F P)
    (hprog : IsStronglyProgressive F X) (hr : HasRightContinuousPaths X P)
    {τ : Ω → WithTop ℝ≥0} (hτ : IsStoppingTime F τ) {T : ℝ≥0}
    (hbound : ∀ ω, τ ω ≤ T) : IsReducingStoppingTime X F P τ := by
  refine ⟨hτ, hX.stoppedProcess_of_progressive hprog hr hτ, ?_⟩
  exact ((hX.integrable_stoppedValue_of_bounded hprog hr hτ hbound).uniformIntegrable_condExp
    F.le).ae_eq fun t ↦ by
      have h := hX.stoppedValue_min_ae_eq_condExp_of_bounded hprog hr
        (isStoppingTime_const F t) hτ hbound
      rw [IsStoppingTime.measurableSpace_const] at h
      exact h.symm

end MeasureTheory.Martingale
