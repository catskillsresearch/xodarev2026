/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.FiniteVariation.CompensatorContinuity
public import StochLean.Probability.Process.LocalMartingale.TotallyInaccessibleJumps

/-! # Continuous canonical compensators classify nonnegative jumps

On the actual locally integrable-variation domain, totally inaccessible
positive-time jumps force the sole selected predictable compensator to be
continuous. Conversely, if the source positive-time jumps are nonnegative,
subtracting that actual continuous compensator gives a native local
martingale with the same jumps, so the source jumps are totally inaccessible.

Nonnegative jumps are weaker than monotone paths: continuous signed movement
is unrestricted. Neither the source initial value nor its initial moment is
constrained, and no competitor or candidate compensator is supplied.
-/

@[expose] public section

open MeasureTheory Filter
open scoped NNReal

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
  {F : Filtration ℝ≥0 mΩ} {X : ℝ≥0 → Ω → ℝ}

namespace HasLocallyIntegrableVariation

/-- For an adapted cadlag locally-IV source with nonnegative positive-time
jumps, those jumps are totally inaccessible exactly when its actual selected
predictable compensator is continuous. No condition is imposed on time zero. -/
theorem hasTotallyInaccessibleJumps_iff_hasContinuousPaths_predictableCompensator
    (hv : HasLocallyIntegrableVariation X F P) (ha : Adapted F X) (hF : F.IsUsual P)
    (hc : HasCadlagPaths X P)
    (hj : ∀ᵐ ω ∂P, ∀ t : ℝ≥0, 0 < t → 0 ≤ jumpProcess X t ω) :
    HasTotallyInaccessibleJumps F X P ↔
      HasContinuousPaths (hv.predictableCompensator ha hF hc) P := by
  constructor
  · exact hv.hasContinuousPaths_predictableCompensator_of_totallyInaccessibleJumps ha hF hc
  · intro hA
    obtain ⟨_, _, _, _, hM⟩ := hv.predictableCompensator_properties ha hF hc
    exact hasTotallyInaccessibleJumps_of_localMartingale_sub_continuous hM hF hc hA hj

end HasLocallyIntegrableVariation
end ProbabilityTheory
