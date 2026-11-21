/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Martingale.OptionalSampling.ContinuousClosingUpperTime
public import StochLean.Probability.Process.Stopping.TerminalMeasurable

/-! # Protter I.16 for lower-closed supermartingales

Both stopping times may be infinite and need only be ordered almost everywhere.
The native stopping owner uses the closing input's terminal projection. The
unprojected formula has an explicit terminal measurability hypothesis. Lower
closure is not replaced by equality or uniform integrability.
-/

@[expose] public section

open ProbabilityTheory Filter
open scoped NNReal ENNReal Topology

namespace MeasureTheory.Supermartingale

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsFiniteMeasure P]
  {F : Filtration ℝ≥0 mΩ} {X : ℝ≥0 → Ω → ℝ} {Y : Ω → ℝ}

theorem stoppedValue_closingProjection_optionalSampling_of_le
    (hX : Supermartingale X F P) (hF : F.IsUsual P)
    (hr : HasRightContinuousPaths X P) (hY : Integrable Y P)
    (hclose : ∀ t, P[Y | F t] ≤ᵐ[P] X t)
    {σ τ : Ω → WithTop ℝ≥0} (hσ : IsStoppingTime F σ) (hτ : IsStoppingTime F τ)
    (hle : ∀ ω, σ ω ≤ τ ω) :
    P[stoppedValueWithTerminal X P[Y | ⨆ t, F t] τ | hσ.measurableSpace] ≤ᵐ[P]
      stoppedValueWithTerminal X P[Y | ⨆ t, F t] σ := by
  classical
  let Z := P[Y | ⨆ t, F t]
  have hiτ := hX.integrable_stoppedValue_closingProjection hF hr hY hclose hτ
  have hfin (n : ℕ) : ∀ᵐ ω ∂P, σ ω ≤ (n : ℝ≥0) →
      P[stoppedValueWithTerminal X Z τ | hσ.measurableSpace] ω ≤
        stoppedValueWithTerminal X Z σ ω := by
    have hs := hX.condExp_closingProjection_stoppedValue_le_of_bounded_lower_time hF hr
      hY hclose (hσ.min_const (n : ℝ≥0)) hτ
      (fun ω ↦ (min_le_left _ _).trans (hle ω)) (fun _ ↦ min_le_right _ _)
    have hc := condExp_min_stopping_time_ae_eq_restrict_le_const
      (f := stoppedValueWithTerminal X Z τ) (μ := P) hσ (n : ℝ≥0)
    rw [Filter.EventuallyEq, ae_restrict_iff'
      (hσ.measurableSpace_le _ (hσ.measurableSet_le' (n : ℝ≥0)))] at hc
    filter_upwards [hs, hc] with ω hsω hcω hb
    rw [hcω hb] at hsω
    have hn : σ ω ≠ ⊤ := ne_top_of_le_ne_top WithTop.coe_ne_top hb
    simpa only [stoppedValueWithTerminal_of_ne_top hn, stoppedValue, min_eq_left hb] using hsω
  have hA : MeasurableSet[hσ.measurableSpace] {ω | σ ω = ⊤} :=
    (measurableSet_singleton _).preimage hσ.measurable
  have hWA : {ω | σ ω = ⊤}.indicator (stoppedValueWithTerminal X Z τ) =
      {ω | σ ω = ⊤}.indicator Z := by
    funext ω
    by_cases ht : σ ω = ⊤
    · have htτ : τ ω = ⊤ := top_le_iff.mp (ht ▸ hle ω)
      simp [Set.indicator, ht, stoppedValueWithTerminal_of_top htτ]
    · simp [Set.indicator, ht]
  have hinf : P[stoppedValueWithTerminal X Z τ | hσ.measurableSpace] =ᵐ[
      P.restrict {ω | σ ω = ⊤}] Z := by
    rw [ae_eq_restrict_iff_indicator_ae_eq (hσ.measurableSpace_le _ hA)]
    refine (condExp_indicator hiτ hA).symm.trans ?_
    rw [hWA]
    have hmZ : StronglyMeasurable[⨆ t, F t] Z := stronglyMeasurable_condExp
    exact condExp_of_aestronglyMeasurable' hσ.measurableSpace_le
      (hmZ.indicator_stoppingTime_eq_top hσ).aestronglyMeasurable
      ((integrable_condExp : Integrable Z P).indicator (hσ.measurableSpace_le _ hA))
  rw [Filter.EventuallyEq, ae_restrict_iff' (hσ.measurableSpace_le _ hA)] at hinf
  filter_upwards [eventually_countable_forall.mpr hfin, hinf] with ω hfinω hinfω
  by_cases ht : σ ω = ⊤
  · simpa only [stoppedValueWithTerminal_of_top ht] using (hinfω ht).le
  · lift σ ω to ℝ≥0 using ht with t ht
    obtain ⟨n, hn⟩ := exists_nat_ge t
    exact hfinω n (WithTop.coe_le_coe.mpr hn)

theorem stoppedValue_closingProjection_optionalSampling
    (hX : Supermartingale X F P) (hF : F.IsUsual P)
    (hr : HasRightContinuousPaths X P) (hY : Integrable Y P)
    (hclose : ∀ t, P[Y | F t] ≤ᵐ[P] X t)
    {σ τ : Ω → WithTop ℝ≥0} (hσ : IsStoppingTime F σ) (hτ : IsStoppingTime F τ)
    (hle : ∀ᵐ ω ∂P, σ ω ≤ τ ω) :
    P[stoppedValueWithTerminal X P[Y | ⨆ t, F t] τ | hσ.measurableSpace] ≤ᵐ[P]
      stoppedValueWithTerminal X P[Y | ⨆ t, F t] σ := by
  have he : σ =ᵐ[P] (fun ω ↦ min (σ ω) (τ ω)) :=
    hle.mono fun _ hω ↦ (min_eq_left hω).symm
  have hf := hσ.measurableSpace_congr_ae_of_usual (hσ.min hτ) hF he
  have h := hX.stoppedValue_closingProjection_optionalSampling_of_le hF hr hY hclose
    (hσ.min hτ) hτ (fun _ ↦ min_le_right _ _)
  rw [← hf] at h
  filter_upwards [h, he] with ω hω heω
  have hv := congrArg (fun t : WithTop ℝ≥0 ↦
    stoppedValueWithTerminal X P[Y | ⨆ t, F t] (fun _ : Ω ↦ t) ω) heω
  exact hω.trans_eq hv.symm

theorem stoppedValue_terminalMeasurable_closing_optionalSampling
    (hX : Supermartingale X F P) (hF : F.IsUsual P)
    (hr : HasRightContinuousPaths X P) (hY : Integrable Y P)
    (hm : StronglyMeasurable[⨆ t, F t] Y) (hclose : ∀ t, P[Y | F t] ≤ᵐ[P] X t)
    {σ τ : Ω → WithTop ℝ≥0} (hσ : IsStoppingTime F σ) (hτ : IsStoppingTime F τ)
    (hle : ∀ᵐ ω ∂P, σ ω ≤ τ ω) :
    P[stoppedValueWithTerminal X Y τ | hσ.measurableSpace] ≤ᵐ[P]
      stoppedValueWithTerminal X Y σ := by
  have h := hX.stoppedValue_closingProjection_optionalSampling hF hr hY hclose hσ hτ hle
  rwa [condExp_of_stronglyMeasurable (iSup_le F.le) hm hY] at h

theorem stoppedValue_zeroTerminal_optionalSampling
    (hX : Supermartingale X F P) (hF : F.IsUsual P)
    (hr : HasRightContinuousPaths X P) (hn : ∀ t, 0 ≤ᵐ[P] X t)
    {σ τ : Ω → WithTop ℝ≥0} (hσ : IsStoppingTime F σ) (hτ : IsStoppingTime F τ)
    (hle : ∀ᵐ ω ∂P, σ ω ≤ τ ω) :
    P[stoppedValueWithTerminal X 0 τ | hσ.measurableSpace] ≤ᵐ[P]
      stoppedValueWithTerminal X 0 σ := by
  exact hX.stoppedValue_terminalMeasurable_closing_optionalSampling hF hr (integrable_zero Ω ℝ P)
    stronglyMeasurable_zero (fun t ↦ by simpa only [condExp_zero] using hn t) hσ hτ hle

end MeasureTheory.Supermartingale
