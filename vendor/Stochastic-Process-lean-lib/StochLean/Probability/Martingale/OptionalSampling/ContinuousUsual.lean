/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Martingale.OptionalSampling.ContinuousStopping
public import StochLean.Probability.Process.Path.Stopping

/-!
# Optional sampling under the usual conditions

The original process need only have right-continuous paths on one full-measure
event. We use a progressive, everywhere-regular indistinguishable version, then
transport stopped values. Completeness places the exceptional null sets in
each stopping-time sigma-algebra. No joint measurability of arbitrary values
assigned on the exceptional trajectories is asserted.
-/

@[expose] public section

open ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology

namespace MeasureTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {F : Filtration ℝ≥0 mΩ}
  {P : Measure Ω} {X : ℝ≥0 → Ω → ℝ}

theorem StronglyAdapted.exists_progressive_indistinguishable_of_usual
    (hX : StronglyAdapted F X) (hF : F.IsUsual P) (hr : HasRightContinuousPaths X P) :
    ∃ Y : ℝ≥0 → Ω → ℝ, Indistinguishable X Y P ∧ IsStronglyProgressive F Y ∧
      ∀ ω, IsRightContinuousPath (Y · ω) := by
  obtain ⟨Y, hmod, hprog, hreg⟩ :=
    hX.exists_isStronglyProgressive_modification_of_hasRightContinuousPaths hF hr
  exact ⟨Y, hmod.indistinguishable_of_rightContinuous hr (ae_of_all _ hreg), hprog, hreg⟩

theorem StronglyAdapted.measurable_stoppedValue_of_usual
    (hX : StronglyAdapted F X) (hF : F.IsUsual P) (hr : HasRightContinuousPaths X P)
    {τ : Ω → WithTop ℝ≥0} (hτ : IsStoppingTime F τ) :
    Measurable[hτ.measurableSpace] (stoppedValue X τ) := by
  obtain ⟨Y, heq, hprog, _⟩ := hX.exists_progressive_indistinguishable_of_usual hF hr
  have hc : IsCompleteSubMeasurableSpace P hτ.measurableSpace := fun A hA ↦
    hτ.le_measurableSpace_of_const_le (fun _ ↦ bot_le) A (hF.complete_initial A hA)
  exact hc.measurable_congr_ae (measurable_stoppedValue hprog hτ) (heq.stoppedValue τ).symm

theorem StronglyAdapted.stoppedProcess_of_usual
    (hX : StronglyAdapted F X) (hF : F.IsUsual P) (hr : HasRightContinuousPaths X P)
    {τ : Ω → WithTop ℝ≥0} (hτ : IsStoppingTime F τ) :
    StronglyAdapted F (MeasureTheory.stoppedProcess X τ) := by
  obtain ⟨Y, heq, hprog, _⟩ := hX.exists_progressive_indistinguishable_of_usual hF hr
  intro t
  have hc : IsCompleteSubMeasurableSpace P (F t) := fun A hA ↦
    F.mono bot_le A (hF.complete_initial A hA)
  exact (hc.measurable_congr_ae (hprog.stronglyAdapted_stoppedProcess hτ t).measurable
    ((heq.stoppedProcess τ).ae_eq t).symm).stronglyMeasurable

namespace Martingale

variable [IsFiniteMeasure P] [SigmaFiniteFiltration P F]

theorem stoppedValue_ae_eq_condExp_of_bounded_usual (hX : Martingale X F P)
    (hF : F.IsUsual P) (hr : HasRightContinuousPaths X P)
    {τ : Ω → WithTop ℝ≥0} (hτ : IsStoppingTime F τ) {T : ℝ≥0}
    (hbound : ∀ ω, τ ω ≤ T) : stoppedValue X τ =ᵐ[P] P[X T | hτ.measurableSpace] := by
  obtain ⟨Y, heq, hprog, hreg⟩ :=
    hX.stronglyAdapted.exists_progressive_indistinguishable_of_usual hF hr
  have hY := hX.congr hprog.stronglyAdapted heq.ae_eq
  exact (heq.stoppedValue τ).trans
    ((hY.stoppedValue_ae_eq_condExp_of_bounded hprog (ae_of_all _ hreg) hτ hbound).trans
      (condExp_congr_ae (heq.ae_eq T)).symm)

theorem integrable_stoppedValue_of_bounded_usual (hX : Martingale X F P)
    (hF : F.IsUsual P) (hr : HasRightContinuousPaths X P)
    {τ : Ω → WithTop ℝ≥0} (hτ : IsStoppingTime F τ) {T : ℝ≥0}
    (hbound : ∀ ω, τ ω ≤ T) : Integrable (stoppedValue X τ) P :=
  integrable_condExp.congr
    (hX.stoppedValue_ae_eq_condExp_of_bounded_usual hF hr hτ hbound).symm

theorem stoppedValue_ae_eq_condExp_of_bounded_le_usual (hX : Martingale X F P)
    (hF : F.IsUsual P) (hr : HasRightContinuousPaths X P)
    {σ τ : Ω → WithTop ℝ≥0} (hσ : IsStoppingTime F σ) (hτ : IsStoppingTime F τ)
    (hστ : σ ≤ τ) {T : ℝ≥0} (hbound : ∀ ω, τ ω ≤ T) :
    stoppedValue X σ =ᵐ[P] P[stoppedValue X τ | hσ.measurableSpace] := by
  have hs := hX.stoppedValue_ae_eq_condExp_of_bounded_usual hF hr hσ
    (fun ω ↦ (hστ ω).trans (hbound ω))
  have ht := hX.stoppedValue_ae_eq_condExp_of_bounded_usual hF hr hτ hbound
  exact hs.trans ((condExp_condExp_of_le (hσ.measurableSpace_mono hτ hστ)
    hτ.measurableSpace_le).symm.trans (condExp_congr_ae ht).symm)

/-- The minimum formula retains the sigma-field at the original, possibly unbounded or
infinite, first time. Only the terminal time requires a deterministic bound. -/
theorem stoppedValue_min_ae_eq_condExp_of_bounded_usual (hX : Martingale X F P)
    (hF : F.IsUsual P) (hr : HasRightContinuousPaths X P)
    {σ τ : Ω → WithTop ℝ≥0} (hσ : IsStoppingTime F σ) (hτ : IsStoppingTime F τ)
    {T : ℝ≥0} (hbound : ∀ ω, τ ω ≤ T) :
    stoppedValue X (fun ω ↦ min (σ ω) (τ ω)) =ᵐ[P]
      P[stoppedValue X τ | hσ.measurableSpace] := by
  obtain ⟨Y, heq, hp, hreg⟩ :=
    hX.stronglyAdapted.exists_progressive_indistinguishable_of_usual hF hr
  have hY := hX.congr hp.stronglyAdapted heq.ae_eq
  exact (heq.stoppedValue _).trans
    ((hY.stoppedValue_min_ae_eq_condExp_of_bounded hp (ae_of_all _ hreg) hσ hτ hbound).trans
      (condExp_congr_ae (heq.stoppedValue τ)).symm)

theorem stoppedProcess_of_usual (hX : Martingale X F P)
    (hF : F.IsUsual P) (hr : HasRightContinuousPaths X P)
    {τ : Ω → WithTop ℝ≥0} (hτ : IsStoppingTime F τ) :
    Martingale (stoppedProcess X τ) F P := by
  obtain ⟨Y, heq, hprog, hreg⟩ :=
    hX.stronglyAdapted.exists_progressive_indistinguishable_of_usual hF hr
  exact ((hX.congr hprog.stronglyAdapted heq.ae_eq).stoppedProcess_of_rightContinuous
    hreg hτ).congr (hX.stronglyAdapted.stoppedProcess_of_usual hF hr hτ)
      (fun t ↦ ((heq.stoppedProcess τ).ae_eq t).symm)

theorem isReducingStoppingTime_of_bounded_usual (hX : Martingale X F P)
    (hF : F.IsUsual P) (hr : HasRightContinuousPaths X P)
    {τ : Ω → WithTop ℝ≥0} (hτ : IsStoppingTime F τ) {T : ℝ≥0}
    (hbound : ∀ ω, τ ω ≤ T) : IsReducingStoppingTime X F P τ := by
  obtain ⟨Y, heq, hprog, hreg⟩ :=
    hX.stronglyAdapted.exists_progressive_indistinguishable_of_usual hF hr
  have hu := (hX.congr hprog.stronglyAdapted heq.ae_eq).isReducingStoppingTime_of_bounded
    hprog (ae_of_all _ hreg) hτ hbound
  exact ⟨hτ, hX.stoppedProcess_of_usual hF hr hτ,
    hu.2.2.ae_eq (fun t ↦ ((heq.stoppedProcess τ).ae_eq t).symm)⟩

end Martingale
end MeasureTheory
