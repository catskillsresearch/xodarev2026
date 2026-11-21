/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.Semimartingale.PredictableQuadraticVariation
public import StochLean.Probability.Process.FiniteVariation.ContinuousCompensator
public import StochLean.Probability.Process.Path.ContinuousOfJump

/-! # The angle process of an AE-continuous semimartingale

The actual raw quadratic variation of an AE-continuous source is itself
AE-continuous. An existing predictable version, not an assertion about
arbitrary exceptional raw trajectories, proves its locally integrable
variation. Common-path invariance then transfers the actual selected
compensator back to the original raw process.

The angle process is indistinguishable from raw quadratic variation minus
the time-constant original initial square. Raw quadratic variation starts
at `X 0 ^ 2` almost surely, whereas the angle process starts exactly at zero.
Thus direct equality with the raw process is asserted only for zero initial
value. No first or second initial moment is imposed, and no new bracket,
compensator, or predictable-version selector is defined.
-/

@[expose] public section

open MeasureTheory Filter
open scoped NNReal

namespace ProbabilityTheory.IsSemimartingale

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
  {F : Filtration ℝ≥0 mΩ} {X : ℝ≥0 → Ω → ℝ}

/-- Positive jumps of the actual raw bracket vanish for an AE-continuous
source. The initial square is not included in that zero-jump condition. -/
theorem hasContinuousPaths_quadraticVariation_of_hasContinuousPaths
    (hX : IsSemimartingale X F P) (hF : F.IsUsual P) (hc : HasContinuousPaths X P) :
    HasContinuousPaths (hX.quadraticVariation hF) P := by
  apply (hX.hasCadlagPaths_quadraticVariation hF).hasContinuousPaths_of_jumpProcess_eq_zero
  filter_upwards [hX.jumpProcess_quadraticVariation hF, hc] with ω hj hω t ht
  rw [hj t, IsContinuousPath.jumpProcess_eq_zero hω ht, zero_pow (by decide : 2 ≠ 0)]

/-- The original raw bracket is actually locally integrable in variation.
The proof uses a predictable version and transfers back by common-path
equality, without claiming predictability of arbitrary exceptional paths. -/
theorem hasLocallyIntegrableVariation_quadraticVariation_of_hasContinuousPaths
    (hX : IsSemimartingale X F P) (hF : F.IsUsual P) (hc : HasContinuousPaths X P) :
    HasLocallyIntegrableVariation (hX.quadraticVariation hF) F P :=
  MeasureTheory.Adapted.hasLocallyIntegrableVariation_of_continuous_finiteVariation
    (hX.adapted_quadraticVariation hF) hF
    (hX.hasContinuousPaths_quadraticVariation_of_hasContinuousPaths hF hc)
    (hX.hasFiniteVariationPaths_quadraticVariation hF)

/-- For an AE-continuous semimartingale, the selected angle process equals
the actual raw bracket after subtracting the original initial square.
Its domain proof is constructed, not supplied as a candidate hypothesis. -/
theorem predictableQuadraticVariation_eq_sub_initial_sq_of_hasContinuousPaths
    (hX : IsSemimartingale X F P) (hF : F.IsUsual P) (hc : HasContinuousPaths X P) :
    Indistinguishable (hX.predictableQuadraticVariation hF
      (hX.hasLocallyIntegrableVariation_quadraticVariation_of_hasContinuousPaths hF hc))
      (hX.quadraticVariation hF - fun _ ω ↦ (X 0 ω) ^ 2) P := by
  let hQ := hX.hasLocallyIntegrableVariation_quadraticVariation_of_hasContinuousPaths hF hc
  have he := hQ.predictableCompensator_eq_sub_initial_of_hasContinuousPaths
    (hX.adapted_quadraticVariation hF) hF
    (hX.hasContinuousPaths_quadraticVariation_of_hasContinuousPaths hF hc)
  filter_upwards [he, hX.quadraticVariation_zero_ae hF] with ω hω h0 t
  change hQ.predictableCompensator _ hF _ t ω =
    hX.quadraticVariation hF t ω - (X 0 ω) ^ 2
  have h := hω t
  change hQ.predictableCompensator _ hF _ t ω =
    hX.quadraticVariation hF t ω - hX.quadraticVariation hF 0 ω at h
  rw [h, h0]

/-- Zero initial value is precisely the normalization used here to identify
the angle process directly with the actual raw quadratic variation. -/
theorem predictableQuadraticVariation_eq_raw_of_hasContinuousPaths_of_initial_zero
    (hX : IsSemimartingale X F P) (hF : F.IsUsual P) (hc : HasContinuousPaths X P)
    (h0 : X 0 =ᵐ[P] 0) :
    Indistinguishable (hX.predictableQuadraticVariation hF
      (hX.hasLocallyIntegrableVariation_quadraticVariation_of_hasContinuousPaths hF hc))
      (hX.quadraticVariation hF) P := by
  filter_upwards [hX.predictableQuadraticVariation_eq_sub_initial_sq_of_hasContinuousPaths hF hc,
    h0] with ω hω hzero t
  simpa only [Pi.sub_apply, hzero, Pi.zero_apply, zero_pow (by decide : 2 ≠ 0), sub_zero]
    using hω t

end ProbabilityTheory.IsSemimartingale
