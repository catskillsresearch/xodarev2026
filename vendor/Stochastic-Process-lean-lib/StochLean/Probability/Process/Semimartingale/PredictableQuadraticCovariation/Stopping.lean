/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.FiniteVariation.CompensatorStopping
public import StochLean.Probability.Process.Semimartingale.PredictableQuadraticCovariation
public import StochLean.Probability.Process.Semimartingale.QuadraticVariation.Stopping
public import StochLean.Probability.Process.Semimartingale.QuadraticCovariation.Stopping

/-! # Arbitrary stopping of the actual angle processes

The already proved raw bracket stopping identities transport locally
integrable variation to the actual brackets of the stopped sources. The
sole predictable compensator's congruence and stopping theorem then identify
the selected stopped angle with the stopped selected angle.

Both the square and mixed constructions use their actual transported domain
proofs, not an extra existence premise. The lifetime may be zero or infinite
and need only be a stopping time. Original raw initial squares and products
are retained; the angle processes themselves remain zero-initial. No initial
moment or predictable-lifetime assumption is imposed.
-/

@[expose] public section

open MeasureTheory
open scoped NNReal

namespace ProbabilityTheory.IsSemimartingale

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
  {F : Filtration ℝ≥0 mΩ} {X Y : ℝ≥0 → Ω → ℝ} {τ : Ω → WithTop ℝ≥0}

/-- Arbitrary stopping preserves the actual raw square bracket's legal
compensator domain, by the established raw stopping identity. -/
theorem hasLocallyIntegrableVariation_quadraticVariation_stoppedProcess
    (hX : IsSemimartingale X F P) (hF : F.IsUsual P)
    (hQ : HasLocallyIntegrableVariation (hX.quadraticVariation hF) F P)
    (hτ : IsStoppingTime F τ) :
    HasLocallyIntegrableVariation ((hX.stoppedProcess hF hτ).quadraticVariation hF) F P :=
  (hQ.stoppedProcess (hX.adapted_quadraticVariation hF) hF
    (hX.hasCadlagPaths_quadraticVariation hF) hτ).congr
      (hX.quadraticVariation_stoppedProcess hF hτ).symm

/-- The actual square angle commutes with every stopping time. The stopped
domain proof is constructed, including at zero and infinite lifetime. -/
theorem predictableQuadraticVariation_stoppedProcess
    (hX : IsSemimartingale X F P) (hF : F.IsUsual P)
    (hQ : HasLocallyIntegrableVariation (hX.quadraticVariation hF) F P)
    (hτ : IsStoppingTime F τ) :
    let hQτ : HasLocallyIntegrableVariation
        ((hX.stoppedProcess hF hτ).quadraticVariation hF) F P :=
      hX.hasLocallyIntegrableVariation_quadraticVariation_stoppedProcess hF hQ hτ
    Indistinguishable ((hX.stoppedProcess hF hτ).predictableQuadraticVariation hF hQτ)
      (MeasureTheory.stoppedProcess (hX.predictableQuadraticVariation hF hQ) τ) P := by
  let hS := hX.stoppedProcess hF hτ
  let hQτ := hX.hasLocallyIntegrableVariation_quadraticVariation_stoppedProcess hF hQ hτ
  have hs := hQ.stoppedProcess (hX.adapted_quadraticVariation hF) hF
    (hX.hasCadlagPaths_quadraticVariation hF) hτ
  have he := hQτ.predictableCompensator_congr hs (hS.adapted_quadraticVariation hF)
    ((hX.adapted_quadraticVariation hF).stronglyAdapted.stoppedProcess_of_usual hF
      (hX.hasCadlagPaths_quadraticVariation hF).hasRightContinuousPaths hτ).adapted hF
    (hS.hasCadlagPaths_quadraticVariation hF)
    ((hX.hasCadlagPaths_quadraticVariation hF).stoppedProcess τ)
    (hX.quadraticVariation_stoppedProcess hF hτ)
  exact he.trans (hQ.predictableCompensator_stoppedProcess
    (hX.adapted_quadraticVariation hF) hF (hX.hasCadlagPaths_quadraticVariation hF) hτ)

/-- Simultaneously stopping both sources preserves the actual mixed raw
bracket's locally integrable variation, without assuming a stopped domain. -/
theorem hasLocallyIntegrableVariation_quadraticCovariation_stoppedProcess_both
    (hX : IsSemimartingale X F P) (hY : IsSemimartingale Y F P) (hF : F.IsUsual P)
    (hQ : HasLocallyIntegrableVariation (hX.quadraticCovariation hY hF) F P)
    (hτ : IsStoppingTime F τ) :
    HasLocallyIntegrableVariation
      ((hX.stoppedProcess hF hτ).quadraticCovariation (hY.stoppedProcess hF hτ) hF) F P :=
  (hQ.stoppedProcess (hX.adapted_quadraticCovariation hY hF) hF
    (hX.hasCadlagPaths_quadraticCovariation hY hF) hτ).congr
      (hX.quadraticCovariation_stoppedProcess_both hY hF hτ).symm

/-- The actual mixed angle of two simultaneously stopped sources is their
original mixed angle stopped at the same arbitrary lifetime. -/
theorem predictableQuadraticCovariation_stoppedProcess_both
    (hX : IsSemimartingale X F P) (hY : IsSemimartingale Y F P) (hF : F.IsUsual P)
    (hQ : HasLocallyIntegrableVariation (hX.quadraticCovariation hY hF) F P)
    (hτ : IsStoppingTime F τ) :
    let hQτ : HasLocallyIntegrableVariation
        ((hX.stoppedProcess hF hτ).quadraticCovariation (hY.stoppedProcess hF hτ) hF) F P :=
      hX.hasLocallyIntegrableVariation_quadraticCovariation_stoppedProcess_both hY hF hQ hτ
    Indistinguishable
      ((hX.stoppedProcess hF hτ).predictableQuadraticCovariation
        (hY.stoppedProcess hF hτ) hF hQτ)
      (MeasureTheory.stoppedProcess (hX.predictableQuadraticCovariation hY hF hQ) τ) P := by
  let hSX := hX.stoppedProcess hF hτ
  let hSY := hY.stoppedProcess hF hτ
  let hQτ :=
    hX.hasLocallyIntegrableVariation_quadraticCovariation_stoppedProcess_both hY hF hQ hτ
  have hs := hQ.stoppedProcess (hX.adapted_quadraticCovariation hY hF) hF
    (hX.hasCadlagPaths_quadraticCovariation hY hF) hτ
  have he := hQτ.predictableCompensator_congr hs (hSX.adapted_quadraticCovariation hSY hF)
    ((hX.adapted_quadraticCovariation hY hF).stronglyAdapted.stoppedProcess_of_usual hF
      (hX.hasCadlagPaths_quadraticCovariation hY hF).hasRightContinuousPaths hτ).adapted hF
    (hSX.hasCadlagPaths_quadraticCovariation hSY hF)
    ((hX.hasCadlagPaths_quadraticCovariation hY hF).stoppedProcess τ)
    (hX.quadraticCovariation_stoppedProcess_both hY hF hτ)
  exact he.trans (hQ.predictableCompensator_stoppedProcess
    (hX.adapted_quadraticCovariation hY hF) hF
    (hX.hasCadlagPaths_quadraticCovariation hY hF) hτ)

end ProbabilityTheory.IsSemimartingale
