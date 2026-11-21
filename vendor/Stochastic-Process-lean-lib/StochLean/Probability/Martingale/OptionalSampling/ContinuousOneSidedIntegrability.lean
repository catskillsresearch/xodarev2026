/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.Stopping.UpperApproxPartition
public import StochLean.Probability.Martingale.OptionalSampling.ContinuousTime

/-! # Integrability at bounded stopping times for one-sided martingales

Uniform first-moment bounds of the actual upper approximations and Fatou's
lemma prove integrability of their right-continuous limit. No uniform
integrability or L1 convergence of the approximating family is assumed.
No path boundedness, nonnegativity or usual-filtration assumption is needed.
The conditional optional-sampling inequality remains a separate step.
-/

@[expose] public section

open ProbabilityTheory Filter
open scoped NNReal ENNReal Topology

namespace MeasureTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsFiniteMeasure P]
  {F : Filtration ℝ≥0 mΩ} {X : ℝ≥0 → Ω → ℝ}

theorem Supermartingale.eLpNorm_finiteStoppingTime_value_le (hX : Supermartingale X F P)
    (τ : FiniteStoppingTime F) {T : ℝ≥0} (hb : ∀ ω, τ ω ≤ T)
    (hr : HasRightContinuousPaths X P) :
    eLpNorm (fun ω ↦ X (τ ω) ω) 1 P ≤
      ENNReal.ofReal ((∫ ω, X 0 ω ∂P) + 2 * (∫ ω, ‖X T ω‖ ∂P)) := by
  apply Lp.eLpNorm_le_of_ae_tendsto (u := atTop)
    (f := fun n ω ↦ X (τ.upperApprox T n ω) ω)
  · apply Eventually.of_forall
    intro n
    rw [eLpNorm_one_eq_lintegral_enorm,
      ← ofReal_integral_norm_eq_lintegral_enorm (hX.integrable_upperApprox_value τ T n)]
    exact ENNReal.ofReal_le_ofReal (hX.integral_norm_upperApprox_value_le τ T n)
  · exact fun n ↦ (hX.integrable_upperApprox_value τ T n).aestronglyMeasurable
  · exact Martingale.ae_tendsto_upperApprox_value τ hb hr

theorem Supermartingale.integrable_finiteStoppingTime_value (hX : Supermartingale X F P)
    (τ : FiniteStoppingTime F) {T : ℝ≥0} (hb : ∀ ω, τ ω ≤ T)
    (hr : HasRightContinuousPaths X P) : Integrable (fun ω ↦ X (τ ω) ω) P := by
  apply memLp_one_iff_integrable.mp
  refine ⟨?_, (hX.eLpNorm_finiteStoppingTime_value_le τ hb hr).trans_lt ENNReal.ofReal_lt_top⟩
  exact aestronglyMeasurable_of_tendsto_ae _
    (fun n ↦ (hX.integrable_upperApprox_value τ T n).aestronglyMeasurable)
    (Martingale.ae_tendsto_upperApprox_value τ hb hr)

theorem Submartingale.integrable_finiteStoppingTime_value (hX : Submartingale X F P)
    (τ : FiniteStoppingTime F) {T : ℝ≥0} (hb : ∀ ω, τ ω ≤ T)
    (hr : HasRightContinuousPaths X P) : Integrable (fun ω ↦ X (τ ω) ω) P := by
  have hrn : HasRightContinuousPaths (-X) P := hr.mono fun _ hω t ↦ (hω t).neg
  have h : Integrable (-(fun ω ↦ X (τ ω) ω)) P :=
    hX.neg.integrable_finiteStoppingTime_value τ hb hrn
  exact integrable_neg_iff.mp h

theorem Supermartingale.integrable_stoppedValue_of_bounded (hX : Supermartingale X F P)
    {τ : Ω → WithTop ℝ≥0} (hτ : IsStoppingTime F τ) {T : ℝ≥0}
    (hb : ∀ ω, τ ω ≤ T) (hr : HasRightContinuousPaths X P) : Integrable (stoppedValue X τ) P := by
  have hn (ω) : τ ω ≠ ⊤ := ne_top_of_le_ne_top WithTop.coe_ne_top (hb ω)
  let σ := FiniteStoppingTime.ofNotTop hτ hn
  have he : σ.withTop = τ := FiniteStoppingTime.withTop_ofNotTop hτ hn
  have hs (ω) : σ ω ≤ T := by
    apply WithTop.coe_le_coe.mp
    change σ.withTop ω ≤ (T : WithTop ℝ≥0)
    rw [he]
    exact hb ω
  rw [← he, FiniteStoppingTime.stoppedValue_eq]
  exact hX.integrable_finiteStoppingTime_value σ hs hr

theorem Submartingale.integrable_stoppedValue_of_bounded (hX : Submartingale X F P)
    {τ : Ω → WithTop ℝ≥0} (hτ : IsStoppingTime F τ) {T : ℝ≥0}
    (hb : ∀ ω, τ ω ≤ T) (hr : HasRightContinuousPaths X P) : Integrable (stoppedValue X τ) P := by
  have hrn : HasRightContinuousPaths (-X) P := hr.mono fun _ hω t ↦ (hω t).neg
  simpa only [stoppedValue_neg, integrable_neg_iff] using
    hX.neg.integrable_stoppedValue_of_bounded hτ hb hrn

end MeasureTheory
