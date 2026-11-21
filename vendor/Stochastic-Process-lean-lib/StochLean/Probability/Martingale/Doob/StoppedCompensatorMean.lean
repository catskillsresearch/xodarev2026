/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Martingale.OptionalSampling.ContinuousOneSidedStopping
public import StochLean.Probability.Martingale.Doob.ContinuousComparison

/-! # Mean bounds for ordinary stopping and stopped compensators

Minimum optional sampling with a bounded deterministic upper endpoint compares
the source mean with the ordinary stopped-process mean. The lifetime itself
may be unbounded or infinite; the sampled minimum is finite. No Class D or
convergence of stopped samples is assumed.

For an already given true martingale decomposition of the stopped process,
the existing expectation identity bounds the compensator's mean by the
original supermartingale mean drop. This is an auxiliary estimate for actual
decompositions, not an existence theorem or a compensator certificate.
-/

@[expose] public section

open ProbabilityTheory Filter
open scoped NNReal

namespace MeasureTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsFiniteMeasure P]
  {F : Filtration ℝ≥0 mΩ} {X B : ℝ≥0 → Ω → ℝ} {τ : Ω → WithTop ℝ≥0}

/-- The ordinary stopped value has mean at least the original mean at every
finite time, even when the stopping lifetime can be infinite. -/
theorem Supermartingale.integral_le_integral_stoppedProcess
    (hX : Supermartingale X F P) (hF : F.IsUsual P)
    (hr : HasRightContinuousPaths X P) (hτ : IsStoppingTime F τ) (t : ℝ≥0) :
    (∫ ω, X t ω ∂P) ≤ ∫ ω, stoppedProcess X τ t ω ∂P := by
  have hi : Integrable (stoppedProcess X τ t) P :=
    (hX.stoppedProcess_of_usual hF hr hτ).integrable t
  have hs := hX.condExp_stoppedValue_min_ae_le_of_bounded hF hr hτ
    (isStoppingTime_const F t) (fun _ ↦ le_rfl)
  have hCE : P[X t | hτ.measurableSpace] ≤ᵐ[P] stoppedProcess X τ t := by
    have heConst : stoppedValue X (fun _ ↦ (t : WithTop ℝ≥0)) = X t := rfl
    have heMin : stoppedValue X (fun ω ↦ min (τ ω) (t : WithTop ℝ≥0)) =
        stoppedProcess X τ t := by
      funext ω
      change X (min (τ ω) (t : WithTop ℝ≥0)).untopA ω =
        X (min (t : WithTop ℝ≥0) (τ ω)).untopA ω
      rw [min_comm]
    rwa [heConst, heMin] at hs
  have hh := integral_mono_ae integrable_condExp hi hCE
  rwa [integral_condExp hτ.measurableSpace_le] at hh

/-- A given zero-initial compensator of the ordinarily stopped process has
mean bounded by the original source mean drop. Only this compensator
coordinate's integrability is required; no path property of it is needed. -/
theorem Martingale.integral_compensator_le_supermartingale_drop
    (hM : Martingale (stoppedProcess X τ + B) F P) (hX : Supermartingale X F P)
    (hF : F.IsUsual P) (hr : HasRightContinuousPaths X P) (hτ : IsStoppingTime F τ)
    (hB0 : B 0 =ᵐ[P] 0) (t : ℝ≥0) (hiB : Integrable (B t) P) :
    (∫ ω, B t ω ∂P) ≤ (∫ ω, X 0 ω ∂P) - ∫ ω, X t ω ∂P := by
  have hi : Integrable (stoppedProcess X τ t) P :=
    (hX.stoppedProcess_of_usual hF hr hτ).integrable t
  have he := hM.integral_add_compensator_eq hB0 t hi hiB
  have hzero : stoppedProcess X τ 0 = X 0 := by
    funext ω
    exact stoppedProcess_eq_of_le (show ((0 : ℝ≥0) : WithTop ℝ≥0) ≤ τ ω from bot_le)
  rw [hzero] at he
  rw [he]
  exact sub_le_sub_left (hX.integral_le_integral_stoppedProcess hF hr hτ t) _

end MeasureTheory
