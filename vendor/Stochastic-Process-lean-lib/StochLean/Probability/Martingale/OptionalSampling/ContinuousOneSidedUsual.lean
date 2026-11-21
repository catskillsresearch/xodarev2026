/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Martingale.OptionalSampling.ContinuousOneSided
public import StochLean.Probability.Martingale.OptionalSampling.ContinuousUsual
public import StochLean.Probability.Process.Stopping.MeasurableSpaceCongruence

/-! # One-sided optional sampling under the usual conditions -/

@[expose] public section

open ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology

namespace MeasureTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {F : Filtration ℝ≥0 mΩ}
  {P : Measure Ω} {X : ℝ≥0 → Ω → ℝ}
  [IsFiniteMeasure P] [SigmaFiniteFiltration P F]

theorem Submartingale.finiteStoppingTime_value_ae_le_condExp_of_le
    (hX : Submartingale X F P) (hF : F.IsUsual P) (hr : HasRightContinuousPaths X P)
    (σ τ : FiniteStoppingTime F) (hle : ∀ ω, σ ω ≤ τ ω) {T : ℝ≥0} (hb : ∀ ω, τ ω ≤ T) :
    (fun ω ↦ X (σ ω) ω) ≤ᵐ[P] P[(fun ω ↦ X (τ ω) ω) | σ.measurableSpace] := by
  obtain ⟨Y, hm, hp, hc⟩ :=
    hX.stronglyAdapted.exists_isStronglyProgressive_modification_of_hasRightContinuousPaths hF hr
  have hY := hX.congr hp.stronglyAdapted hm
  have hrc : HasRightContinuousPaths Y P := Eventually.of_forall hc
  have he := hm.indistinguishable_of_rightContinuous hr hrc
  have hσ : (fun ω ↦ X (σ ω) ω) =ᵐ[P] (fun ω ↦ Y (σ ω) ω) :=
    he.mono fun ω hω ↦ hω (σ ω)
  have hτ : (fun ω ↦ X (τ ω) ω) =ᵐ[P] (fun ω ↦ Y (τ ω) ω) :=
    he.mono fun ω hω ↦ hω (τ ω)
  have hsample :=
    hY.finiteStoppingTime_value_ae_le_condExp_of_le_of_progressive hp hrc σ τ hle hb
  exact (Filter.eventuallyLE_congr hσ (condExp_congr_ae hτ)).mpr hsample

theorem Supermartingale.condExp_finiteStoppingTime_value_ae_le_of_le
    (hX : Supermartingale X F P) (hF : F.IsUsual P) (hr : HasRightContinuousPaths X P)
    (σ τ : FiniteStoppingTime F) (hle : ∀ ω, σ ω ≤ τ ω) {T : ℝ≥0} (hb : ∀ ω, τ ω ≤ T) :
    P[(fun ω ↦ X (τ ω) ω) | σ.measurableSpace] ≤ᵐ[P] (fun ω ↦ X (σ ω) ω) := by
  have hneg : HasRightContinuousPaths (-X) P := hr.mono fun _ hω t ↦ (hω t).neg
  have h := hX.neg.finiteStoppingTime_value_ae_le_condExp_of_le hF hneg σ τ hle hb
  change (fun ω ↦ -X (σ ω) ω) ≤ᵐ[P]
    P[-(fun ω ↦ X (τ ω) ω) | σ.measurableSpace] at h
  filter_upwards [h, condExp_neg (fun ω ↦ X (τ ω) ω) σ.measurableSpace] with ω hω heω
  rw [heω] at hω
  exact neg_le_neg_iff.mp hω

theorem Submartingale.stoppedValue_ae_le_condExp_of_bounded
    (hX : Submartingale X F P) (hF : F.IsUsual P) (hr : HasRightContinuousPaths X P)
    {σ τ : Ω → WithTop ℝ≥0} (hσ : IsStoppingTime F σ) (hτ : IsStoppingTime F τ)
    (hle : ∀ ω, σ ω ≤ τ ω) {T : ℝ≥0} (hb : ∀ ω, τ ω ≤ T) :
    stoppedValue X σ ≤ᵐ[P] P[stoppedValue X τ | hσ.measurableSpace] := by
  have hτf (ω) : τ ω ≠ ⊤ := ne_top_of_le_ne_top WithTop.coe_ne_top (hb ω)
  have hσf (ω) : σ ω ≠ ⊤ := ne_top_of_le_ne_top (hτf ω) (hle ω)
  let S := FiniteStoppingTime.ofNotTop hσ hσf
  let U := FiniteStoppingTime.ofNotTop hτ hτf
  have hSe : S.withTop = σ := FiniteStoppingTime.withTop_ofNotTop hσ hσf
  have hUe : U.withTop = τ := FiniteStoppingTime.withTop_ofNotTop hτ hτf
  have hSU (ω) : S ω ≤ U ω := by
    apply WithTop.coe_le_coe.mp
    change S.withTop ω ≤ U.withTop ω
    rw [hSe, hUe]
    exact hle ω
  have hUT (ω) : U ω ≤ T := by
    apply WithTop.coe_le_coe.mp
    change U.withTop ω ≤ (T : WithTop ℝ≥0)
    rw [hUe]
    exact hb ω
  have h := hX.finiteStoppingTime_value_ae_le_condExp_of_le hF hr S U hSU hUT
  have hSf : S.measurableSpace = hσ.measurableSpace :=
    FiniteStoppingTime.measurableSpace_ofNotTop hσ hσf
  simpa only [← FiniteStoppingTime.stoppedValue_eq, hSe, hUe, hSf] using h

theorem Supermartingale.condExp_stoppedValue_ae_le_of_bounded
    (hX : Supermartingale X F P) (hF : F.IsUsual P) (hr : HasRightContinuousPaths X P)
    {σ τ : Ω → WithTop ℝ≥0} (hσ : IsStoppingTime F σ) (hτ : IsStoppingTime F τ)
    (hle : ∀ ω, σ ω ≤ τ ω) {T : ℝ≥0} (hb : ∀ ω, τ ω ≤ T) :
    P[stoppedValue X τ | hσ.measurableSpace] ≤ᵐ[P] stoppedValue X σ := by
  have hneg : HasRightContinuousPaths (-X) P := hr.mono fun _ hω t ↦ (hω t).neg
  have h := hX.neg.stoppedValue_ae_le_condExp_of_bounded hF hneg hσ hτ hle hb
  filter_upwards [h, condExp_neg (stoppedValue X τ) hσ.measurableSpace] with ω hω heω
  simpa only [stoppedValue_neg, Pi.neg_apply, heω, neg_le_neg_iff] using hω

/-- Usual completeness permits almost-everywhere ordering and a bound that
fails on a null set. The original stopping sigma-field is retained exactly. -/
theorem Submartingale.stoppedValue_ae_le_condExp_of_ae_bounded
    (hX : Submartingale X F P) (hF : F.IsUsual P) (hr : HasRightContinuousPaths X P)
    {σ τ : Ω → WithTop ℝ≥0} (hσ : IsStoppingTime F σ) (hτ : IsStoppingTime F τ)
    (hle : ∀ᵐ ω ∂P, σ ω ≤ τ ω) {T : ℝ≥0} (hb : ∀ᵐ ω ∂P, τ ω ≤ T) :
    stoppedValue X σ ≤ᵐ[P] P[stoppedValue X τ | hσ.measurableSpace] := by
  let U : Ω → WithTop ℝ≥0 := fun ω ↦ min (τ ω) (T : WithTop ℝ≥0)
  let S : Ω → WithTop ℝ≥0 := fun ω ↦ min (σ ω) (U ω)
  have hU : IsStoppingTime F U := hτ.min_const T
  have hS : IsStoppingTime F S := hσ.min hU
  have heU : τ =ᵐ[P] U := hb.mono fun _ hω ↦ (min_eq_left hω).symm
  have heS : σ =ᵐ[P] S := by
    filter_upwards [hle, heU] with ω hω heω
    exact (min_eq_left (hω.trans_eq heω)).symm
  have hf := hσ.measurableSpace_congr_ae_of_usual hS hF heS
  have hvS : stoppedValue X σ =ᵐ[P] stoppedValue X S :=
    heS.mono fun ω hω ↦ congrArg (fun r : WithTop ℝ≥0 ↦ X r.untopA ω) hω
  have hvU : stoppedValue X τ =ᵐ[P] stoppedValue X U :=
    heU.mono fun ω hω ↦ congrArg (fun r : WithTop ℝ≥0 ↦ X r.untopA ω) hω
  have h := hX.stoppedValue_ae_le_condExp_of_bounded hF hr hS hU
    (fun _ ↦ min_le_right _ _) (fun _ ↦ min_le_right _ _)
  rw [← hf] at h
  exact (Filter.eventuallyLE_congr hvS (condExp_congr_ae hvU)).mpr h

theorem Supermartingale.condExp_stoppedValue_ae_le_of_ae_bounded
    (hX : Supermartingale X F P) (hF : F.IsUsual P) (hr : HasRightContinuousPaths X P)
    {σ τ : Ω → WithTop ℝ≥0} (hσ : IsStoppingTime F σ) (hτ : IsStoppingTime F τ)
    (hle : ∀ᵐ ω ∂P, σ ω ≤ τ ω) {T : ℝ≥0} (hb : ∀ᵐ ω ∂P, τ ω ≤ T) :
    P[stoppedValue X τ | hσ.measurableSpace] ≤ᵐ[P] stoppedValue X σ := by
  have hneg : HasRightContinuousPaths (-X) P := hr.mono fun _ hω t ↦ (hω t).neg
  have h := hX.neg.stoppedValue_ae_le_condExp_of_ae_bounded hF hneg hσ hτ hle hb
  filter_upwards [h, condExp_neg (stoppedValue X τ) hσ.measurableSpace] with ω hω heω
  simpa only [stoppedValue_neg, Pi.neg_apply, heω, neg_le_neg_iff] using hω

/-- The expectation of a right-continuous supermartingale at a bounded finite
stopping time is at most its initial expectation. -/
theorem Supermartingale.integral_finiteStoppingTime_value_le_initial_of_usual
    (hX : Supermartingale X F P) (hF : F.IsUsual P)
    (hr : HasRightContinuousPaths X P) (τ : FiniteStoppingTime F)
    {T : ℝ≥0} (hb : ∀ ω, τ ω ≤ T) :
    (∫ ω, X (τ ω) ω ∂P) ≤ ∫ ω, X 0 ω ∂P := by
  obtain ⟨Y, heq, hprog, hreg⟩ :=
    hX.stronglyAdapted.exists_progressive_indistinguishable_of_usual hF hr
  have hY : Supermartingale Y F P := hX.congr hprog.stronglyAdapted heq.ae_eq
  let σ : FiniteStoppingTime F := FiniteStoppingTime.const F 0
  have hle := hY.condExp_finiteStoppingTime_value_ae_le_of_le_of_progressive
    hprog (ae_of_all P hreg) σ τ (fun _ ↦ bot_le) hb
  have hiτ := hY.integrable_finiteStoppingTime_value τ hb (ae_of_all P hreg)
  have hint : (∫ ω, Y (τ ω) ω ∂P) ≤ ∫ ω, Y 0 ω ∂P := by
    have h := integral_mono_ae integrable_condExp (hY.integrable 0) hle
    rw [integral_condExp σ.measurableSpace_le] at h
    exact h
  calc
    (∫ ω, X (τ ω) ω ∂P) = ∫ ω, Y (τ ω) ω ∂P :=
      integral_congr_ae (heq.mono fun ω hω ↦ hω (τ ω))
    _ ≤ ∫ ω, Y 0 ω ∂P := hint
    _ = ∫ ω, X 0 ω ∂P := integral_congr_ae (heq.ae_eq 0).symm

end MeasureTheory
