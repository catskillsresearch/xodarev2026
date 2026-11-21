/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.Stopping.Approximation
public import Mathlib.Probability.Martingale.OptionalSampling
public import Mathlib.MeasureTheory.Function.ConditionalExpectation.Real

/-!
# Bounded optional sampling in continuous time

Upper countable-range stopping times are capped at the deterministic bound.
Their values are conditional expectations of one integrable terminal value,
so they are uniformly integrable. Right continuity yields the almost-sure
limit, and Vitali gives L1 convergence. No bounded-path assumption is used.

The core statement assumes progressive measurability and common-event right
continuity. An everywhere-right-continuous adapted martingale has the former
property by the existing ProcessCore theorem. Transport from an AE regular
version under a usual filtration is kept separate.
-/

@[expose] public section

open ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology

namespace MeasureTheory.Martingale

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {F : Filtration ℝ≥0 mΩ}
  {P : Measure Ω} {X : ℝ≥0 → Ω → ℝ} [IsFiniteMeasure P] [SigmaFiniteFiltration P F]

omit [IsFiniteMeasure P] in
private theorem upperApprox_value_ae_eq_condExp (hX : Martingale X F P)
    (τ : FiniteStoppingTime F) (T : ℝ≥0) (n : ℕ) :
    (fun ω ↦ X (τ.upperApprox T n ω) ω) =ᵐ[P]
      P[X T | (τ.upperApprox T n).measurableSpace] := by
  let σ := τ.upperApprox T n
  have hcount : (Set.range σ.withTop).Countable := by
    apply ((τ.countable_range_upperApprox T n).image
      (fun s : ℝ≥0 ↦ (s : WithTop ℝ≥0))).mono
    rintro t ⟨ω, rfl⟩
    exact ⟨σ ω, ⟨ω, rfl⟩, rfl⟩
  exact hX.stoppedValue_ae_eq_condExp_of_le_const_of_countable_range σ.isStoppingTime
    (fun ω ↦ WithTop.coe_le_coe.mpr (τ.upperApprox_le_horizon T n ω)) hcount

theorem uniformIntegrable_upperApprox_value (hX : Martingale X F P)
    (τ : FiniteStoppingTime F) (T : ℝ≥0) :
    UniformIntegrable (fun n ω ↦ X (τ.upperApprox T n ω) ω) 1 P :=
  ((hX.integrable T).uniformIntegrable_condExp
    (fun n ↦ (τ.upperApprox T n).measurableSpace_le)).ae_eq
      (fun n ↦ (upperApprox_value_ae_eq_condExp hX τ T n).symm)

omit [IsFiniteMeasure P] [SigmaFiniteFiltration P F] in
theorem ae_tendsto_upperApprox_value (τ : FiniteStoppingTime F) {T : ℝ≥0}
    (hτ : ∀ ω, τ ω ≤ T) (hr : HasRightContinuousPaths X P) :
    ∀ᵐ ω ∂P, Tendsto (fun n ↦ X (τ.upperApprox T n ω) ω) atTop (𝓝 (X (τ ω) ω)) := by
  filter_upwards [hr] with ω hω
  exact (hω (τ ω)).tendsto.comp (τ.tendsto_upperApprox hτ ω)

theorem integrable_finiteStoppingTime_value (hX : Martingale X F P)
    (τ : FiniteStoppingTime F) {T : ℝ≥0} (hτ : ∀ ω, τ ω ≤ T)
    (hr : HasRightContinuousPaths X P) : Integrable (fun ω ↦ X (τ ω) ω) P :=
  (hX.uniformIntegrable_upperApprox_value τ T).integrable_of_ae_tendsto
    (ae_tendsto_upperApprox_value τ hτ hr)

theorem tendsto_eLpNorm_upperApprox_value (hX : Martingale X F P)
    (τ : FiniteStoppingTime F) {T : ℝ≥0} (hτ : ∀ ω, τ ω ≤ T)
    (hr : HasRightContinuousPaths X P) :
    Tendsto (fun n ↦ eLpNorm
      ((fun ω ↦ X (τ.upperApprox T n ω) ω) - (fun ω ↦ X (τ ω) ω)) 1 P) atTop (𝓝 0) := by
  have hui := hX.uniformIntegrable_upperApprox_value τ T
  have hlim := ae_tendsto_upperApprox_value τ hτ hr
  exact tendsto_Lp_finite_of_tendsto_ae le_rfl (by simp) hui.1
    (hui.memLp_of_ae_tendsto hlim) hui.2.1 hlim

/-- Protter I.17, bounded terminal sampling. Progressivity is stated explicitly;
the source right-continuous adapted version is the next corollary. -/
theorem finiteStoppingTime_value_ae_eq_condExp_of_progressive
    (hX : Martingale X F P) (hprog : IsStronglyProgressive F X)
    (hr : HasRightContinuousPaths X P) (τ : FiniteStoppingTime F)
    {T : ℝ≥0} (hτ : ∀ ω, τ ω ≤ T) :
    (fun ω ↦ X (τ ω) ω) =ᵐ[P] P[X T | τ.measurableSpace] := by
  have hint := hX.integrable_finiteStoppingTime_value τ hτ hr
  have hmeas : StronglyMeasurable[τ.measurableSpace] (fun ω ↦ X (τ ω) ω) :=
    (measurable_stoppedValue hprog τ.isStoppingTime).stronglyMeasurable
  apply ae_eq_condExp_of_forall_setIntegral_eq τ.measurableSpace_le (hX.integrable T)
    (fun _ _ _ ↦ hint.integrableOn) ?_ hmeas.aestronglyMeasurable
  intro A hA _
  have hlim := tendsto_setIntegral_of_L1' (fun ω ↦ X (τ ω) ω) hint.aestronglyMeasurable
    (Eventually.of_forall fun n ↦ memLp_one_iff_integrable.mp
      ((hX.uniformIntegrable_upperApprox_value τ T).memLp n))
    (hX.tendsto_eLpNorm_upperApprox_value τ hτ hr) A
  have heq (n : ℕ) :
      (∫ ω in A, X (τ.upperApprox T n ω) ω ∂P) = ∫ ω in A, X T ω ∂P := by
    have hle : τ.measurableSpace ≤ (τ.upperApprox T n).measurableSpace :=
      τ.isStoppingTime.measurableSpace_mono (τ.upperApprox T n).isStoppingTime
        (fun ω ↦ WithTop.coe_le_coe.mpr (τ.le_upperApprox hτ n ω))
    calc
      _ = ∫ ω in A, P[X T | (τ.upperApprox T n).measurableSpace] ω ∂P :=
        integral_congr_ae (ae_restrict_of_ae (upperApprox_value_ae_eq_condExp hX τ T n))
      _ = _ := setIntegral_condExp (τ.upperApprox T n).measurableSpace_le
        (hX.integrable T) (hle A hA)
  exact tendsto_nhds_unique hlim (by simpa only [heq] using
    (tendsto_const_nhds : Tendsto (fun _ : ℕ ↦ ∫ ω in A, X T ω ∂P) atTop (𝓝 _)))

theorem finiteStoppingTime_value_ae_eq_condExp
    (hX : Martingale X F P) (hr : ∀ ω, IsRightContinuousPath (X · ω))
    (τ : FiniteStoppingTime F) {T : ℝ≥0} (hτ : ∀ ω, τ ω ≤ T) :
    (fun ω ↦ X (τ ω) ω) =ᵐ[P] P[X T | τ.measurableSpace] :=
  hX.finiteStoppingTime_value_ae_eq_condExp_of_progressive
    (hX.stronglyAdapted.isStronglyProgressive_of_rightContinuous hr) (ae_of_all _ hr) τ hτ

/-- Optional sampling between two bounded finite stopping times, using the tower property. -/
theorem finiteStoppingTime_value_ae_eq_condExp_of_le
    (hX : Martingale X F P) (hprog : IsStronglyProgressive F X)
    (hr : HasRightContinuousPaths X P) (σ τ : FiniteStoppingTime F)
    (hστ : ∀ ω, σ ω ≤ τ ω) {T : ℝ≥0} (hτ : ∀ ω, τ ω ≤ T) :
    (fun ω ↦ X (σ ω) ω) =ᵐ[P] P[(fun ω ↦ X (τ ω) ω) | σ.measurableSpace] := by
  have hle : σ.measurableSpace ≤ τ.measurableSpace :=
    σ.isStoppingTime.measurableSpace_mono τ.isStoppingTime
      (fun ω ↦ WithTop.coe_le_coe.mpr (hστ ω))
  have hs := hX.finiteStoppingTime_value_ae_eq_condExp_of_progressive hprog hr σ
    (fun ω ↦ (hστ ω).trans (hτ ω))
  have ht := hX.finiteStoppingTime_value_ae_eq_condExp_of_progressive hprog hr τ hτ
  exact hs.trans ((condExp_condExp_of_le hle τ.measurableSpace_le).symm.trans
    (condExp_congr_ae ht).symm)

end MeasureTheory.Martingale
