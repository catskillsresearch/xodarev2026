/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.FiniteVariation.CanonicalCompensator
public import StochLean.Probability.Process.Stopping.PredictableProcess

/-! # Stopping the actual predictable compensator

Actual stopped variation remains locally integrable along the original
localizers. Predictability is preserved by any stopping time, not only by
predictable times. Full compensator uniqueness therefore identifies the
selected compensator of the stopped source with the stopped selected
compensator. Zero and infinite lifetimes retain the original initial value;
neither an initial moment nor predictable-lifetime restriction is imposed.
-/

@[expose] public section

open MeasureTheory Filter
open scoped NNReal

namespace ProbabilityTheory.HasLocallyIntegrableVariation

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
  {F : Filtration ℝ≥0 mΩ} {X : ℝ≥0 → Ω → ℝ} {τ : Ω → WithTop ℝ≥0}

/-- Actual local variation integrability is stable under arbitrary stopping. -/
theorem stoppedProcess (hv : HasLocallyIntegrableVariation X F P)
    (ha : Adapted F X) (hF : F.IsUsual P) (hc : HasCadlagPaths X P)
    (hτ : IsStoppingTime F τ) :
    HasLocallyIntegrableVariation (MeasureTheory.stoppedProcess X τ) F P := by
  obtain ⟨ρ, hρ, hvρ⟩ := hasLocallyIntegrableVariation_iff_exists_stopped.mp hv
  refine hasLocallyIntegrableVariation_iff_exists_stopped.mpr ⟨ρ, hρ, fun n ↦ ?_⟩
  have haρ := (ha.stronglyAdapted.stoppedProcess_of_usual hF hc.hasRightContinuousPaths
    (hρ.isStoppingTime n)).adapted
  have hs := (hvρ n).stoppedProcess haρ hF (hc.stoppedProcess (ρ n)) hτ
  simpa only [MeasureTheory.stoppedProcess_stoppedProcess, inf_comm] using hs

variable [IsProbabilityMeasure P]

/-- The sole selected compensator commutes with stopping up to one common
path event. The source's actual stopped-domain proof is constructed. -/
theorem predictableCompensator_stoppedProcess
    (hv : HasLocallyIntegrableVariation X F P) (ha : Adapted F X) (hF : F.IsUsual P)
    (hc : HasCadlagPaths X P) (hτ : IsStoppingTime F τ) :
    Indistinguishable
      ((hv.stoppedProcess ha hF hc hτ).predictableCompensator
        (ha.stronglyAdapted.stoppedProcess_of_usual hF hc.hasRightContinuousPaths hτ).adapted
        hF (hc.stoppedProcess τ))
      (MeasureTheory.stoppedProcess (hv.predictableCompensator ha hF hc) τ) P := by
  obtain ⟨hpA, _, hA0, hvA, hM⟩ := hv.predictableCompensator_properties ha hF hc
  have hp := hpA.stoppedProcess hτ
  apply (hv.stoppedProcess ha hF hc hτ).predictableCompensator_unique
    (ha.stronglyAdapted.stoppedProcess_of_usual hF hc.hasRightContinuousPaths hτ).adapted
    hF (hc.stoppedProcess τ) hp (hvA.hasFiniteVariationPaths.stoppedProcess τ)
  · exact Eventually.of_forall fun ω ↦ by
      rw [MeasureTheory.stoppedProcess_eq_of_le
        (i := (0 : ℝ≥0)) (τ := τ) bot_le]
      exact congrFun hA0 ω
  · exact hM.stoppedProcess hF hτ

end ProbabilityTheory.HasLocallyIntegrableVariation
