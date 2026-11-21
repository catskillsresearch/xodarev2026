/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.FiniteVariation.CanonicalCompensator
public import StochLean.Probability.Process.FiniteVariation.PredictableJumps
public import StochLean.Probability.Process.Stopping.JumpCoefficients

/-! # Predictable compensators and predictable sources

The already constructed canonical compensator has no jump at a totally
inaccessible stopping time. Positive finite times use actual predictable-FV
jump avoidance. At zero the selected compensator is exactly zero, and at
infinity the stopped jump has its explicitly zero terminal value.

For a predictable source the same canonical compensator is the source minus
its original time-constant initial value. The latter is a genuine Protter
local martingale even without an initial moment. Actual uniqueness therefore
identifies the selected process with the normalized predictable source.

These statements neither impose source monotonicity nor require the stopping
time to be a source jump time. They do not assert continuity of compensators
for a larger class of sources, and introduce no further selector.
-/

@[expose] public section

open MeasureTheory Filter
open scoped NNReal

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
  {F : Filtration ℝ≥0 mΩ} {X : ℝ≥0 → Ω → ℝ}

namespace HasLocallyIntegrableVariation

/-- The actual selected compensator has zero stopped jump at any totally
inaccessible time, with zero initial and infinite-time branches retained. -/
theorem predictableCompensator_stopped_jump_ae_eq_zero_of_totallyInaccessible
    (hv : HasLocallyIntegrableVariation X F P) (ha : Adapted F X) (hF : F.IsUsual P)
    (hc : HasCadlagPaths X P) {τ : Ω → WithTop ℝ≥0}
    (hτ : IsTotallyInaccessibleStoppingTime F τ P) :
    stoppedValueWithTerminal (jumpProcess (hv.predictableCompensator ha hF hc))
      (fun _ ↦ (0 : ℝ)) τ =ᵐ[P] 0 := by
  let B := hv.predictableCompensator ha hF hc
  obtain ⟨hpB, hcB, hB0, hvB, _⟩ := hv.predictableCompensator_properties ha hF hc
  have hj := hpB.ae_jump_eq_zero_at_totallyInaccessibleStoppingTime hF
    (Eventually.of_forall hcB) hvB.hasFiniteVariationPaths hτ
  filter_upwards [hj] with ω hω
  change stoppedValueWithTerminal (jumpProcess B) (fun _ ↦ (0 : ℝ)) τ ω = 0
  cases ht : τ ω with
  | top => exact stoppedValueWithTerminal_jump_eq_zero_of_top ht
  | coe t =>
    rw [stoppedValueWithTerminal_jump_eq_of_eq_coe ht]
    by_cases ht0 : t = 0
    · subst t
      change jumpProcess (hv.predictableCompensator ha hF hc) 0 ω = 0
      simp only [jumpProcess_zero, hB0, Pi.zero_apply]
    · exact hω t (pos_iff_ne_zero.mpr ht0) ht

/-- A predictable source is its own compensator only after subtracting its
original initial value. Neither that value nor the source need be integrable
globally; the original constant initial process is a genuine local martingale. -/
theorem predictableCompensator_eq_sub_initial_of_predictable
    (hv : HasLocallyIntegrableVariation X F P) (ha : Adapted F X) (hF : F.IsUsual P)
    (hc : HasCadlagPaths X P) (hp : IsStronglyPredictable F X) :
    Indistinguishable (hv.predictableCompensator ha hF hc) (X - fun _ ↦ X 0) P := by
  let I : ℝ≥0 → Ω → ℝ := fun _ ↦ X 0
  let B := X - I
  have hI : IsContinuousLocalMartingale I F P :=
    isContinuousLocalMartingale_const_initial (ha 0)
  have haI : Adapted F I := hI.1.1
  have hcI : HasCadlagPaths I P := hI.2.hasCadlagPaths
  have hpI : IsStronglyPredictable F I :=
    haI.isStronglyPredictable_of_leftContinuous (fun _ _ ↦ continuousWithinAt_const)
  have hvI : HasLocallyIntegrableVariation I F P :=
    (hasIntegrableVariation_const (P := P) (X 0)).hasLocallyIntegrableVariation
  have hvB : HasLocallyIntegrableVariation B F P := hv.sub hvI ha haI hF hc hcI
  have hB0 : B 0 =ᵐ[P] 0 := Eventually.of_forall fun ω ↦ sub_self (X 0 ω)
  have hM : IsLocalMartingale (X - B) F P := by
    have he : X - B = I := sub_sub_cancel X I
    rw [he]
    exact hI.1
  exact hv.predictableCompensator_unique ha hF hc (hp.sub hpI)
    hvB.hasFiniteVariationPaths hB0 hM

end HasLocallyIntegrableVariation
end ProbabilityTheory
