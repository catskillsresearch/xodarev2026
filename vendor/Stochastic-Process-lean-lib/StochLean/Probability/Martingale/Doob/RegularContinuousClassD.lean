/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Martingale.Doob.RegularSingleJumpRemoval
public import StochLean.Probability.Process.Stopping.NormExitResidual

/-! # Continuous Doob decomposition for regular Class D supermartingales

There is no bound on the original process or its positive-time jumps.
At each actual capped norm exit, the entire original exit jump has a proved
integrable stopped-measurable coefficient. Subtracting its closed step
leaves a deterministically bounded residual. Actual single-jump compensation
and the regular bounded-jump theorem therefore construct a continuous
increasing part for the stopped process.

Continuous FV uniqueness gives stopped consistency. The existing Class D
localization owner constructs the global part, its actual integrable
terminal and a true UI martingale. Predictable jump regularity is used as
stated; it is not replaced by a total-inaccessibility hypothesis. The
general discontinuous predictable Doob decomposition is a separate result.
-/

@[expose] public section

open ProbabilityTheory Filter
open scoped NNReal ENNReal Topology

namespace MeasureTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
  {F : Filtration ℝ≥0 mΩ} {X : ℝ≥0 → Ω → ℝ}

/-- The full regular Class D continuous Doob construction. The input supplies
neither bounded jumps nor a proposed compensator, localization consistency,
terminal value, integrability of exceptional coefficients, or convergence. -/
theorem Supermartingale.exists_continuous_doob_of_classD_of_predictable_jump_mean_zero
    (hX : Supermartingale X F P) (hXD : IsClassD X F P) (hF : F.IsUsual P)
    (hc : HasCadlagPaths X P)
    (hreg : ∀ (ρ : Ω → WithTop ℝ≥0), IsPredictableStoppingTime F ρ P →
      (∀ᵐ ω ∂P, 0 < ρ ω) →
      (∫ ω, stoppedValueWithTerminal (jumpProcess X) (fun _ ↦ (0 : ℝ)) ρ ω ∂P) = 0)
    (h0 : X 0 =ᵐ[P] 0) :
    ∃ (A : ℝ≥0 → Ω → ℝ) (Z : Ω → ℝ),
      Adapted F A ∧ IsStronglyPredictable F A ∧ (∀ ω, Continuous (A · ω)) ∧
      A 0 = 0 ∧ HasMonotonePaths A P ∧ HasFiniteVariationPaths A P ∧
      IsClassD A F P ∧ Martingale (X + A) F P ∧ HasCadlagPaths (X + A) P ∧
      UniformIntegrable (X + A) 1 P ∧ Integrable Z P ∧
      (∀ᵐ ω ∂P, ∀ t, 0 ≤ A t ω ∧ A t ω ≤ Z ω) ∧
      (∀ᵐ ω ∂P, Tendsto (fun t : ℝ≥0 ↦ A t ω) atTop (𝓝 (Z ω))) ∧
      Tendsto (fun t : ℝ≥0 ↦ eLpNorm (A t - Z) 1 P) atTop (𝓝 0) := by
  let τ := cappedNormExitSequence X
  have hτ : IsPreLocalizingSequence F τ P :=
    (hX.stronglyAdapted.adapted.isLocalizingSequence_cappedNormExitSequence hF hc).1
  have hlocal (n : ℕ) : ∃ A : ℝ≥0 → Ω → ℝ,
      Adapted F A ∧ (∀ ω, Continuous (A · ω)) ∧ A 0 = 0 ∧ HasMonotonePaths A P ∧
      Martingale (stoppedProcess X (τ n) + A) F P := by
    have hs := hX.stoppedProcess_of_usual hF hc.hasRightContinuousPaths (hτ.isStoppingTime n)
    have hs0 : stoppedProcess X (τ n) 0 =ᵐ[P] 0 := by
      filter_upwards [h0] with ω hω
      exact (stoppedProcess_eq_of_le (u := X) (τ := τ n)
        (i := (0 : ℝ≥0)) (ω := ω) bot_le).trans hω
    have hp : ∀ᵐ ω ∂P, 0 < τ n ω :=
      (hc.ae_cappedNormExitSequence_pos h0).mono fun _ hω ↦ hω n
    have hm := hX.stronglyAdapted.adapted.stronglyMeasurable_stopped_jump_of_usual
      hF hc (hτ.isStoppingTime n)
    have hi :=
      (hXD.integrable_and_bound_stopped_jump_cappedNormExitSequence
        hX.stronglyAdapted.adapted hF hc n).1
    have hb : ∀ᵐ ω ∂P, ∀ t : ℝ≥0,
        ‖stoppedProcess X (τ n) t ω -
          {v | τ n v ≤ (t : WithTop ℝ≥0)}.indicator
            (stoppedValueWithTerminal (jumpProcess X) (fun _ ↦ (0 : ℝ)) (τ n)) ω‖ ≤
              ((n + 1 : ℕ) : ℝ) :=
      hc.ae_forall_norm_stoppedProcess_sub_exit_jump_le.mono fun _ hω ↦ hω n
    have hregs : ∀ (ρ : Ω → WithTop ℝ≥0), IsPredictableStoppingTime F ρ P →
        (∀ᵐ ω ∂P, 0 < ρ ω) →
        (∫ ω, stoppedValueWithTerminal (jumpProcess (stoppedProcess X (τ n)))
          (fun _ ↦ (0 : ℝ)) ρ ω ∂P) = 0 :=
      fun _ hρ hpos ↦ hc.integral_stopped_jump_stoppedProcess_eq_zero
        hF (hτ.isStoppingTime n) hreg hρ hpos
    obtain ⟨A, _, ha, _, hAc, hA0, hAm, _, _, hM, _, _, _, _, _, _⟩ :=
      hs.exists_continuous_doob_of_regular_bounded_single_jump_residual
        (hXD.stoppedProcess (hτ.isStoppingTime n)) hF (hc.stoppedProcess (τ n)) hregs hs0
        (hτ.isStoppingTime n) hp hm hi (by positivity) hb
    exact ⟨A, ha, hAc, hA0, hAm, hM⟩
  choose A ha hcont hzero hmono hM using hlocal
  have hcons := hX.continuous_doob_localization_consistency hF hc hcont hzero hmono hM
  exact exists_continuous_doob_decomposition_of_consistent_classD_localization
    hX.stronglyAdapted.adapted hXD hF hc h0 hτ ha hcont hzero hmono hM hcons

end MeasureTheory
