/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.Semimartingale.MeasureChange.AbsoluteContinuousDensityKilling
public import StochLean.Probability.Process.LocalMartingale.StoppedJumpStep
public import StochLean.Probability.Process.FiniteVariation.CanonicalCompensator

/-! # The compensator at the density-killing jump

For a source local martingale `M`, the Lenglart killing time carries the
single step `Delta M_R 1_[R,infinity)`.  Its locally integrable variation is
obtained from the fundamental local-martingale decomposition, so the canonical
predictable compensator is available without an integrability assumption on
`M` itself.  The step vanishes indistinguishably under the target law because
the killing time is target-almost surely infinite.
-/

@[expose] public section

open MeasureTheory Filter Set
open scoped NNReal

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}
  {P Q : Measure Ω} [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
  {F : Filtration ℝ≥0 mΩ} {M : ℝ≥0 → Ω → ℝ}

/-- Protter III.42's process `U_t = Delta M_R 1_{R <= t}`, with terminal
coefficient zero when `R = infinity`. -/
noncomputable def absoluteContinuousKillingJump
    (Q P : Measure Ω) (F : Filtration ℝ≥0 mΩ)
    (M : ℝ≥0 → Ω → ℝ) : ℝ≥0 → Ω → ℝ :=
  stoppedJumpStep M (absoluteContinuousDensityKillingTime Q P F)

/-- The killing-jump step is adapted in the source usual filtration. -/
theorem adapted_absoluteContinuousKillingJump
    (hM : IsLocalMartingale M F P) (hFP : F.IsUsual P) :
    Adapted F (absoluteContinuousKillingJump Q P F M) := by
  exact ProbabilityTheory.Adapted.adapted_stoppedJumpStep_of_usual
    hM.1 hFP hM.2.1
      (isStoppingTime_absoluteContinuousDensityKillingTime (Q := Q) hFP)

/-- The killing-jump step has cadlag paths under every law. -/
theorem hasCadlagPaths_absoluteContinuousKillingJump :
    HasCadlagPaths (absoluteContinuousKillingJump Q P F M) P := by
  exact hasCadlagPaths_stoppedJumpStep M
    (absoluteContinuousDensityKillingTime Q P F)

/-- The actual killing jump has locally integrable variation under the source
law; this is the existence input for its canonical compensator. -/
theorem hasLocallyIntegrableVariation_absoluteContinuousKillingJump
    (hM : IsLocalMartingale M F P) (hFP : F.IsUsual P) :
    HasLocallyIntegrableVariation
      (absoluteContinuousKillingJump Q P F M) F P := by
  exact hM.stoppedJumpStep_hasLocallyIntegrableVariation hFP
    (isStoppingTime_absoluteContinuousDensityKillingTime (Q := Q) hFP)
    (absoluteContinuousDensityKillingTime_pos (Q := Q) (P := P) (F := F))

/-- The canonical predictable compensator `tilde U` of the density-killing
jump used in the Lenglart--Girsanov formula. -/
noncomputable def absoluteContinuousKillingJumpCompensator
    (hM : IsLocalMartingale M F P) (hFP : F.IsUsual P) :
    ℝ≥0 → Ω → ℝ :=
  (hasLocallyIntegrableVariation_absoluteContinuousKillingJump
      (Q := Q) hM hFP).predictableCompensator
    (adapted_absoluteContinuousKillingJump (Q := Q) hM hFP) hFP
    (hasCadlagPaths_absoluteContinuousKillingJump
      (Q := Q) (P := P) (F := F) (M := M))

/-- The selected killing-jump compensator is predictable, cadlag,
zero-initial and locally of integrable variation, and compensation leaves a
source local martingale. -/
theorem absoluteContinuousKillingJumpCompensator_properties
    (hM : IsLocalMartingale M F P) (hFP : F.IsUsual P) :
    let A := absoluteContinuousKillingJumpCompensator (Q := Q) hM hFP
    IsStronglyPredictable F A ∧ (∀ ω, IsCadlagPath (A · ω)) ∧
      A 0 = 0 ∧ HasLocallyIntegrableVariation A F P ∧
      IsLocalMartingale
        (absoluteContinuousKillingJump Q P F M - A) F P := by
  simpa only [absoluteContinuousKillingJumpCompensator] using
    (hasLocallyIntegrableVariation_absoluteContinuousKillingJump
      (Q := Q) hM hFP).predictableCompensator_properties
        (adapted_absoluteContinuousKillingJump (Q := Q) hM hFP) hFP
        (hasCadlagPaths_absoluteContinuousKillingJump
          (Q := Q) (P := P) (F := F) (M := M))

/-- The killing-jump step is identically zero on one target-full-measure
event, since the killing time is target-almost surely infinite. -/
theorem indistinguishable_absoluteContinuousKillingJump_zero
    (hQP : Q ≪ P) (hFP : F.IsUsual P) :
    Indistinguishable (absoluteContinuousKillingJump Q P F M) 0 Q := by
  filter_upwards
      [ae_absoluteContinuousDensityKillingTime_eq_top hQP hFP]
    with ω hω t
  rw [absoluteContinuousKillingJump]
  simp only [stoppedJumpStep, Pi.zero_apply]
  rw [indicator_of_notMem]
  simpa only [mem_setOf_eq, hω, not_le, WithTop.coe_lt_top]

end ProbabilityTheory
