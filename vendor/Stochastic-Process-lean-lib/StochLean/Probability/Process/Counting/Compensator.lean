/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.Counting.Basic
public import StochLean.Probability.Process.FiniteVariation.BoundedJumpLocalization
public import StochLean.Probability.Process.FiniteVariation.CanonicalCompensator

/-! # The actual compensator of a nonexplosive counting process

Unit jumps, monotonicity, and real cadlag paths supply the proved local
integrable-variation domain, without a finite expected count assumption.
The existing canonical compensator is then used directly: this file does
not introduce a second compensator selector or take compensator existence
as an input.

This is the nonexplosive counting-domain consumer of Protter III.22.
General arrival-sequence representation and separate non-Poisson examples
are not established here.
-/

@[expose] public section

open MeasureTheory Filter
open scoped NNReal

namespace ProbabilityTheory.IsNonexplosiveCountingProcess

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
  {F : Filtration ℝ≥0 mΩ} {N : ℝ≥0 → Ω → ℕ}

/-- The real count has locally integrable variation, derived from its
actual unit-jump paths rather than assumed as a compensation certificate. -/
theorem hasLocallyIntegrableVariation_real [IsFiniteMeasure P]
    (hN : IsNonexplosiveCountingProcess N P) (ha : Adapted F N) (hF : F.IsUsual P) :
    HasLocallyIntegrableVariation (fun t ω ↦ (N t ω : ℝ)) F P :=
  hN.hasFiniteVariationPaths_real.hasLocallyIntegrableVariation_of_jump_bound
    ha.natCast_real hF hN.hasCadlagPaths_real zero_le_one hN.ae_norm_jumpProcess_real_le_one

/-- The sole selected predictable compensator is increasing, starts
exactly at zero, and leaves a zero-initial local martingale. Uniqueness is
against all predictable finite-variation competitors with almost-sure
initial zero, not just competitors supplied with a local-IV certificate. -/
theorem predictableCompensator_properties [IsProbabilityMeasure P]
    (hN : IsNonexplosiveCountingProcess N P) (ha : Adapted F N) (hF : F.IsUsual P) :
    let hv := hN.hasLocallyIntegrableVariation_real ha hF
    let A := hv.predictableCompensator ha.natCast_real hF hN.hasCadlagPaths_real
    IsStronglyPredictable F A ∧ (∀ ω, IsCadlagPath (A · ω)) ∧ A 0 = 0 ∧
      HasMonotonePaths A P ∧ HasLocallyIntegrableVariation A F P ∧
      IsLocalMartingale ((fun t ω ↦ (N t ω : ℝ)) - A) F P ∧
      ((fun t ω ↦ (N t ω : ℝ)) - A) 0 =ᵐ[P] 0 ∧
      ∀ B : ℝ≥0 → Ω → ℝ,
        IsStronglyPredictable F B → HasFiniteVariationPaths B P →
        B 0 =ᵐ[P] 0 → IsLocalMartingale ((fun t ω ↦ (N t ω : ℝ)) - B) F P →
          Indistinguishable A B P := by
  dsimp only
  let hv := hN.hasLocallyIntegrableVariation_real ha hF
  let A := hv.predictableCompensator ha.natCast_real hF hN.hasCadlagPaths_real
  obtain ⟨hp, hc, h0, hvA, hM⟩ :=
    hv.predictableCompensator_properties ha.natCast_real hF hN.hasCadlagPaths_real
  refine ⟨hp, hc, h0,
    hv.hasMonotonePaths_predictableCompensator ha.natCast_real hF hN.hasCadlagPaths_real
      hN.hasMonotonePaths_real, hvA, hM, ?_, ?_⟩
  · filter_upwards [hN.initial_real] with ω hω
    change (N 0 ω : ℝ) - A 0 ω = 0
    rw [show A 0 ω = 0 from congrFun h0 ω, sub_zero]
    exact hω
  · intro B hpB hvB hB0 hMB
    exact hv.predictableCompensator_unique ha.natCast_real hF hN.hasCadlagPaths_real
      hpB hvB hB0 hMB

end ProbabilityTheory.IsNonexplosiveCountingProcess
