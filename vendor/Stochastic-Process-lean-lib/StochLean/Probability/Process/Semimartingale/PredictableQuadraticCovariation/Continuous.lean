/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.Semimartingale.PredictableQuadraticCovariation
public import StochLean.Probability.Process.Semimartingale.QuadraticCovariation.ContinuousLeft
public import StochLean.Probability.Process.Semimartingale.QuadraticCovariation.Jump
public import StochLean.Probability.Process.FiniteVariation.ContinuousCompensator
public import StochLean.Probability.Process.Path.ContinuousOfJump

/-! # A continuous argument gives an actual continuous mixed angle

One AE-continuous source removes every positive-time mixed jump. Its actual
raw covariation is therefore AE-continuous FV, which gives local IV and an
actual angle independently of whether the other source has a square angle.
The selected mixed angle agrees with the existing continuous covariation
owner, hence with raw covariation minus the original initial product.
No exceptional raw path is declared predictable, and no initial moment or
continuity of the other source is assumed.
-/

@[expose] public section

open MeasureTheory
open scoped NNReal

namespace ProbabilityTheory.IsSemimartingale

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
  {F : Filtration ℝ≥0 mΩ} {X Y : ℝ≥0 → Ω → ℝ}

/-- One AE-continuous source gives an AE-continuous actual raw mixed bracket. -/
theorem hasContinuousPaths_quadraticCovariation_of_left_continuous
    (hX : IsSemimartingale X F P) (hY : IsSemimartingale Y F P) (hF : F.IsUsual P)
    (hc : HasContinuousPaths X P) :
    HasContinuousPaths (hX.quadraticCovariation hY hF) P := by
  apply (hX.hasCadlagPaths_quadraticCovariation hY hF).hasContinuousPaths_of_jumpProcess_eq_zero
  filter_upwards [hX.jumpProcess_quadraticCovariation hY hF, hc] with ω hj hω t ht
  rw [hj t, hω.jumpProcess_eq_zero ht, zero_mul]

/-- The actual mixed domain exists even if no square-angle domain of the
other semimartingale is supplied. -/
theorem hasLocallyIntegrableVariation_quadraticCovariation_of_left_continuous
    (hX : IsSemimartingale X F P) (hY : IsSemimartingale Y F P) (hF : F.IsUsual P)
    (hc : HasContinuousPaths X P) :
    HasLocallyIntegrableVariation (hX.quadraticCovariation hY hF) F P :=
  MeasureTheory.Adapted.hasLocallyIntegrableVariation_of_continuous_finiteVariation
    (hX.adapted_quadraticCovariation hY hF) hF
    (hX.hasContinuousPaths_quadraticCovariation_of_left_continuous hY hF hc)
    (hX.hasFiniteVariationPaths_quadraticCovariation hY hF)

/-- The actual selected mixed angle is the existing continuous covariation,
with the original initial product removed exactly by the established owner. -/
theorem predictableQuadraticCovariation_eq_continuous_of_left_continuous
    (hX : IsSemimartingale X F P) (hY : IsSemimartingale Y F P) (hF : F.IsUsual P)
    (hc : HasContinuousPaths X P) :
    Indistinguishable (hX.predictableQuadraticCovariation hY hF
      (hX.hasLocallyIntegrableVariation_quadraticCovariation_of_left_continuous hY hF hc))
      (hX.continuousQuadraticCovariation hY hF) P := by
  have hQ := hX.hasLocallyIntegrableVariation_quadraticCovariation_of_left_continuous hY hF hc
  have he := hQ.predictableCompensator_eq_sub_initial_of_hasContinuousPaths
    (hX.adapted_quadraticCovariation hY hF) hF
    (hX.hasContinuousPaths_quadraticCovariation_of_left_continuous hY hF hc)
  filter_upwards [he, hX.quadraticCovariation_zero_ae hY hF,
    hX.continuousQuadraticCovariation_eq_of_left_continuous hY hF hc] with ω ha h0 hcont t
  change hQ.predictableCompensator _ hF _ t ω = hX.continuousQuadraticCovariation hY hF t ω
  calc
    _ = hX.quadraticCovariation hY hF t ω - hX.quadraticCovariation hY hF 0 ω := ha t
    _ = hX.quadraticCovariation hY hF t ω - X 0 ω * Y 0 ω := by rw [h0]
    _ = hX.continuousQuadraticCovariation hY hF t ω := (hcont t).symm

end ProbabilityTheory.IsSemimartingale
