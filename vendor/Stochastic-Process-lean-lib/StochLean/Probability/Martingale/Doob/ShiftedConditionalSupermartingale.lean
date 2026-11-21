/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Martingale.Convergence.ConditionalRegularization
public import StochLean.Probability.Process.Measurability.CadlagVersion
public import StochLean.Probability.Process.Path.RightContinuousOrder
public import StochLean.Probability.Process.Stopping.ConditionalBoundedSampling
public import Mathlib.MeasureTheory.Function.ConditionalExpectation.Real

/-! # Cadlag conditional projections of shifted supermartingales

The future family `X (t + δ)` need not be adapted to the original filtration.
The tower property nevertheless makes its current conditional projection a
supermartingale. Bounded right-continuous paths give right-continuous means,
so the existing Doob regularization constructs a coherent cadlag version.

Bounded stopping-time sampling uses an everywhere-cadlag indistinguishable
version of the original input internally. Thus joint measurability is not
incorrectly inferred from only almost-sure path regularity. The identity is
finally transferred back to the original input on its common path event.
-/

@[expose] public section

open ProbabilityTheory Filter Set
open scoped NNReal Topology

namespace MeasureTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsFiniteMeasure P]
  {F : Filtration ℝ≥0 mΩ} {X : ℝ≥0 → Ω → ℝ}

/-- A shifted future conditional projection is a supermartingale for the
original filtration, without claiming that the shifted input is adapted. -/
theorem Supermartingale.supermartingale_condExp_add_time
    (hX : Supermartingale X F P) (δ : ℝ≥0) :
    Supermartingale (fun t ↦ P[X (t + δ) | F t]) F P := by
  refine ⟨fun _ ↦ stronglyMeasurable_condExp, fun s t hst ↦ ?_,
    fun _ ↦ integrable_condExp⟩
  have hle := condExp_mono (m := F s) integrable_condExp (hX.integrable (s + δ))
    (hX.condExp_ae_le (add_le_add hst (le_refl δ)))
  have hleft := condExp_condExp_of_le (μ := P) (F.mono hst) (F.le t)
    (f := X (t + δ))
  have hright := condExp_condExp_of_le (μ := P)
    (F.mono (le_add_of_nonneg_right (show 0 ≤ δ from bot_le))) (F.le (s + δ))
    (f := X (t + δ))
  exact hleft.trans_le (hright.symm.trans_le hle)

omit [IsFiniteMeasure P] in
private theorem hasRightContinuousPaths_add_time (hr : HasRightContinuousPaths X P)
    (δ : ℝ≥0) : HasRightContinuousPaths (fun t ↦ X (t + δ)) P := by
  filter_upwards [hr] with ω hω t
  exact (hω (t + δ)).comp (f := fun s : ℝ≥0 ↦ s + δ) (x := t)
    (continuous_id.add_const δ).continuousWithinAt
    (fun s hs ↦ add_le_add (show t ≤ s from hs) (le_refl δ))

/-- The version and all bounded stopping identities are constructed from
the input supermartingale. No candidate projection or limit is an input.
The common order bound includes time zero. -/
theorem Supermartingale.exists_cadlag_condExp_add_time_of_bound
    (hX : Supermartingale X F P) (hF : F.IsUsual P) (hc : HasCadlagPaths X P)
    {C : ℝ} (hb : ∀ᵐ ω ∂P, ∀ t, ‖X t ω‖ ≤ C) (δ : ℝ≥0) :
    ∃ Q : ℝ≥0 → Ω → ℝ, Supermartingale Q F P ∧
      (∀ ω, IsCadlagPath (Q · ω)) ∧
      (∀ t, Q t =ᵐ[P] P[X (t + δ) | F t]) ∧
      (∀ᵐ ω ∂P, ∀ t, ‖Q t ω‖ ≤ C ∧ Q t ω ≤ X t ω) ∧
      ∀ (σ : FiniteStoppingTime F) (T : ℝ≥0), (∀ ω, σ ω ≤ T) →
        (fun ω ↦ Q (σ ω) ω) =ᵐ[P]
          P[(fun ω ↦ X (σ ω + δ) ω) | σ.measurableSpace] := by
  have hr : HasRightContinuousPaths (fun t ↦ X (t + δ)) P :=
    hasRightContinuousPaths_add_time hc.hasRightContinuousPaths δ
  have hmean := isRightContinuousPath_integral_of_dominated
    (fun t ↦ (hX.integrable (t + δ)).aestronglyMeasurable) hr
    (integrable_const C) (fun t ↦ hb.mono fun _ hω ↦ hω (t + δ))
  have hmeanQ : IsRightContinuousPath (fun t ↦ ∫ ω, P[X (t + δ) | F t] ω ∂P) := by
    have he : (fun t ↦ ∫ ω, P[X (t + δ) | F t] ω ∂P) =
        fun t ↦ ∫ ω, X (t + δ) ω ∂P := by
      funext t
      exact integral_condExp (F.le t)
    rwa [he]
  obtain ⟨R, hR, hcR, heR, _⟩ :=
    (hX.supermartingale_condExp_add_time δ).exists_cadlag_modification hF hmeanQ
  obtain ⟨Q, hRQ, hpQ, hcQ⟩ :=
    hR.stronglyAdapted.exists_cadlag_indistinguishable_of_usual hF hcR
  have hQ : Supermartingale Q F P := hR.congr hpQ.stronglyAdapted (fun t ↦ hRQ.ae_eq t)
  have hcQ' : HasCadlagPaths Q P := Eventually.of_forall hcQ
  have heQ (t : ℝ≥0) : Q t =ᵐ[P] P[X (t + δ) | F t] :=
    ((heR t).trans (hRQ.ae_eq t)).symm
  have hle (t : ℝ≥0) : Q t ≤ᵐ[P] X t :=
    (heQ t).trans_le
      (hX.condExp_ae_le (le_add_of_nonneg_right (show 0 ≤ δ from bot_le)))
  have hleAll : ∀ᵐ ω ∂P, ∀ t, Q t ω ≤ X t ω :=
    hcQ'.hasRightContinuousPaths.ae_forall_le_of_forall_ae_le hc.hasRightContinuousPaths hle
  have hrNorm : HasRightContinuousPaths (fun t ω ↦ ‖Q t ω‖) P :=
    hcQ'.hasRightContinuousPaths.mono fun _ hω t ↦ (hω t).norm
  have hrC : HasRightContinuousPaths (fun _ : ℝ≥0 ↦ fun _ : Ω ↦ C) P :=
    Eventually.of_forall fun _ _ ↦ continuousWithinAt_const
  have hbQ : ∀ᵐ ω ∂P, ∀ t, ‖Q t ω‖ ≤ C := by
    apply hrNorm.ae_forall_le_of_forall_ae_le hrC
    intro t
    filter_upwards [ae_bdd_norm_condExp_of_ae_bdd_norm (m := F t)
      (hb.mono fun _ hω ↦ hω (t + δ)), heQ t] with ω hbω heω
    simpa only [heω] using hbω
  refine ⟨Q, hQ, hcQ, heQ, ?_, ?_⟩
  · filter_upwards [hbQ, hleAll] with ω hbω hleω t
    exact ⟨hbω t, hleω t⟩
  · intro σ T hσ
    obtain ⟨Z, hXZ, hpZ, hcZ⟩ :=
      hX.stronglyAdapted.exists_cadlag_indistinguishable_of_usual hF hc
    have hmZ : Measurable (Function.uncurry Z) :=
      (hpZ.stronglyAdapted.stronglyMeasurable_uncurry_of_rightContinuous
        (fun ω ↦ (hcZ ω).1)).measurable
    have hmShift : Measurable (Function.uncurry (fun t ↦ Z (t + δ))) :=
      hmZ.comp ((measurable_fst.add_const δ).prodMk measurable_snd)
    have hrShift : HasRightContinuousPaths (fun t ↦ Z (t + δ)) P :=
      hasRightContinuousPaths_add_time
        (Eventually.of_forall fun ω ↦ (hcZ ω).1) δ
    have hbShift : ∀ᵐ ω ∂P, ∀ t, ‖Z (t + δ) ω‖ ≤ C := by
      filter_upwards [hXZ, hb] with ω he hω t
      rw [← he (t + δ)]
      exact hω (t + δ)
    have heShift (t : ℝ≥0) : Q t =ᵐ[P] P[Z (t + δ) | F t] :=
      (heQ t).trans (condExp_congr_ae (hXZ.ae_eq (t + δ)))
    have hs := σ.sample_condExp_of_dominated_rightContinuous_of_usual hσ hF hmShift
      hQ.stronglyAdapted hrShift hcQ'.hasRightContinuousPaths
      (integrable_const C) hbShift hbQ heShift
    apply hs.trans (condExp_congr_ae ?_)
    filter_upwards [hXZ] with ω hω
    exact (hω (σ ω + δ)).symm

end MeasureTheory
