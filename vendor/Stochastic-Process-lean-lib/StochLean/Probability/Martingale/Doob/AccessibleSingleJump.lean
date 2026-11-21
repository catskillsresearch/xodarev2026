/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Martingale.Doob.AccessibleCoefficients
public import StochLean.Probability.Martingale.Doob.CenteredStepSeries
public import StochLean.Probability.Process.FiniteVariation.PredictableStepSeries
public import StochLean.Probability.Process.LocalMartingale.Congr

/-! # Actual compensation of integrable accessible single jumps

The existing accessible-time definition supplies a predictable graph cover.
Its actual disjoint positive refinement decomposes the original coefficient
into stopped-measurable pieces with summable first absolute moments. Each
piece is conditioned before its own predictable lifetime. Their actual step
series constructs the predictable integrable-variation compensator.

The centered series is a genuine UI martingale. Absolute summability and the
common-event graph identity identify it with the original jump minus the
constructed compensator. No infinite-time process value, proposed compensator,
or assumed series convergence enters the source hypotheses.
-/

@[expose] public section

open MeasureTheory Filter Set
open scoped NNReal ENNReal

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsFiniteMeasure P]
  {F : Filtration ℝ≥0 mΩ} {σ : Ω → WithTop ℝ≥0} {D : Ω → ℝ}

/-- An accessible positive L1 jump has an actually constructed predictable
compensator with expected total variation at most its first absolute moment. -/
theorem IsAccessibleStoppingTime.exists_predictable_compensator_indicator
    (hσ : IsAccessibleStoppingTime F σ P) (hF : F.IsUsual P)
    (hpos : ∀ᵐ ω ∂P, 0 < σ ω)
    (hm : StronglyMeasurable[hσ.1.measurableSpace] D) (hi : Integrable D P) :
    ∃ A : ℝ≥0 → Ω → ℝ,
      IsStronglyPredictable F A ∧ HasCadlagPaths A P ∧ A 0 =ᵐ[P] 0 ∧
      HasIntegrableVariation A P ∧
      (∫ ω, (eVariationOn (A · ω) univ).toReal ∂P) ≤ ∫ ω, ‖D ω‖ ∂P ∧
      IsUIMartingale
        ((fun t : ℝ≥0 ↦ {ω | σ ω ≤ (t : WithTop ℝ≥0)}.indicator D) - A) F P := by
  classical
  obtain ⟨Γ, hΓ, hpΓ, _, _, hmC, hiC, hsC, hbC, heC⟩ :=
    hσ.exists_disjoint_predictable_coefficient_decomposition hF hpos hm hi
  let C : ℕ → Ω → ℝ := fun n ↦ {ω | σ ω = Γ n ω ∧ σ ω ≠ ⊤}.indicator D
  let K : ℕ → Ω → ℝ := fun n ↦ P[C n | (hΓ n).1.measurableSpaceBefore]
  have hCK : ∀ n, StronglyMeasurable[(hΓ n).1.measurableSpaceBefore] (K n) :=
    fun _ ↦ stronglyMeasurable_condExp
  have hiK (n : ℕ) : Integrable (K n) P := integrable_condExp
  have hsumC : Summable (fun n ↦ ∫ ω, ‖C n ω‖ ∂P) := by
    simpa only [Real.norm_eq_abs] using hsC.summable
  have hnormK (n : ℕ) : (∫ ω, ‖K n ω‖ ∂P) ≤ ∫ ω, ‖C n ω‖ ∂P :=
    integral_norm_condExp_le (C n)
  have hsumK : Summable (fun n ↦ ∫ ω, ‖K n ω‖ ∂P) :=
    hsumC.of_nonneg_of_le (fun n ↦ integral_nonneg fun ω ↦ norm_nonneg (K n ω)) hnormK
  let A : ℝ≥0 → Ω → ℝ := fun t ω ↦
    ∑' n, {ω | Γ n ω ≤ (t : WithTop ℝ≥0)}.indicator (K n) ω
  have hpA : IsStronglyPredictable F A :=
    isStronglyPredictable_tsum_indicator_stoppingTime_le hΓ hF.complete_initial hCK
  have hvA : HasIntegrableVariation A P :=
    hasIntegrableVariation_tsum_indicator_stoppingTime_le hF hΓ hCK hiK hsumK
  refine ⟨A, hpA, hasCadlagPaths_tsum_indicator_lifetime_le Γ hiK hsumK,
    tsum_indicator_lifetime_le_zero_ae (fun n ↦ Eventually.of_forall (hpΓ n)), hvA, ?_, ?_⟩
  · refine (integral_eVariationOn_tsum_indicator_stoppingTime_le
      hF hΓ hCK hiK hsumK).trans ((hsumK.tsum_le_tsum hnormK hsumC).trans ?_)
    simpa only [Real.norm_eq_abs] using hbC
  · have hUI := isUIMartingale_tsum_indicator_sub_condExp_before
      (fun n ↦ (hΓ n).1) hmC hiC hsumC
    apply hUI.congr
      (fun t ↦ (hm.indicator_stoppingTime_le hσ.1 t).measurable.sub
        (hpA.stronglyAdapted t).measurable)
    filter_upwards [heC, (ae_summable_norm_and_integrable_tsum_norm hiC hsumC).1,
      (ae_summable_norm_and_integrable_tsum_norm hiK hsumK).1] with ω he hC hK t
    have hsCstep : Summable
        (fun n ↦ {ω | Γ n ω ≤ (t : WithTop ℝ≥0)}.indicator (C n) ω) :=
      hC.of_norm_bounded (fun _ ↦ norm_indicator_le_norm_self _ _)
    have hsKstep : Summable
        (fun n ↦ {ω | Γ n ω ≤ (t : WithTop ℝ≥0)}.indicator (K n) ω) :=
      hK.of_norm_bounded (fun _ ↦ norm_indicator_le_norm_self _ _)
    change (∑' n, {ω | Γ n ω ≤ (t : WithTop ℝ≥0)}.indicator (C n - K n) ω) =
      {ω | σ ω ≤ (t : WithTop ℝ≥0)}.indicator D ω - A t ω
    have hsub (n : ℕ) :
        {ω | Γ n ω ≤ (t : WithTop ℝ≥0)}.indicator (C n - K n) ω =
          {ω | Γ n ω ≤ (t : WithTop ℝ≥0)}.indicator (C n) ω -
            {ω | Γ n ω ≤ (t : WithTop ℝ≥0)}.indicator (K n) ω :=
      congrFun (indicator_sub {ω | Γ n ω ≤ (t : WithTop ℝ≥0)} (C n) (K n)) ω
    rw [tsum_congr hsub, hsCstep.tsum_sub hsKstep, ← he t]

end ProbabilityTheory
