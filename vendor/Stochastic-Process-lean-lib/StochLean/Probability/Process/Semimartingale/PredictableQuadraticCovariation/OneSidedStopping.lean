/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.Semimartingale.PredictableQuadraticCovariation.Stopping
public import StochLean.Probability.Process.Semimartingale.QuadraticCovariation.OneSidedStopping

/-! # One-sided stopping of the actual mixed angle

Stopping either source alone gives the original mixed angle stopped at the
same lifetime. The actual raw one-sided identities first construct the new
locally-integrable-variation domain; the sole compensator's congruence and
stopping theorem then supply the selected angle identity.

There is no supplied domain for the changed sources and no additional
selector. Lifetimes may be zero or infinite and need not be predictable.
The raw initial product is retained without an initial moment assumption.
-/

@[expose] public section

open MeasureTheory
open scoped NNReal

namespace ProbabilityTheory.IsSemimartingale

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
  {F : Filtration ℝ≥0 mΩ} {X Y : ℝ≥0 → Ω → ℝ} {τ : Ω → WithTop ℝ≥0}

/-- Stopping only the first source stops the actual selected mixed angle.
The changed raw bracket's domain is proved in the statement's typed let. -/
theorem predictableQuadraticCovariation_stoppedProcess_left
    (hX : IsSemimartingale X F P) (hY : IsSemimartingale Y F P) (hF : F.IsUsual P)
    (hQ : HasLocallyIntegrableVariation (hX.quadraticCovariation hY hF) F P)
    (hτ : IsStoppingTime F τ) :
    let hQτ : HasLocallyIntegrableVariation
        ((hX.stoppedProcess hF hτ).quadraticCovariation hY hF) F P :=
      (hQ.stoppedProcess (hX.adapted_quadraticCovariation hY hF) hF
        (hX.hasCadlagPaths_quadraticCovariation hY hF) hτ).congr
          (hX.quadraticCovariation_stoppedProcess_left hY hF hτ).symm
    Indistinguishable
      ((hX.stoppedProcess hF hτ).predictableQuadraticCovariation hY hF hQτ)
      (MeasureTheory.stoppedProcess (hX.predictableQuadraticCovariation hY hF hQ) τ) P := by
  let hSX := hX.stoppedProcess hF hτ
  have hs := hQ.stoppedProcess (hX.adapted_quadraticCovariation hY hF) hF
    (hX.hasCadlagPaths_quadraticCovariation hY hF) hτ
  let hQτ := hs.congr (hX.quadraticCovariation_stoppedProcess_left hY hF hτ).symm
  have he := hQτ.predictableCompensator_congr hs (hSX.adapted_quadraticCovariation hY hF)
    ((hX.adapted_quadraticCovariation hY hF).stronglyAdapted.stoppedProcess_of_usual hF
      (hX.hasCadlagPaths_quadraticCovariation hY hF).hasRightContinuousPaths hτ).adapted hF
    (hSX.hasCadlagPaths_quadraticCovariation hY hF)
    ((hX.hasCadlagPaths_quadraticCovariation hY hF).stoppedProcess τ)
    (hX.quadraticCovariation_stoppedProcess_left hY hF hτ)
  exact he.trans (hQ.predictableCompensator_stoppedProcess
    (hX.adapted_quadraticCovariation hY hF) hF
    (hX.hasCadlagPaths_quadraticCovariation hY hF) hτ)

/-- Stopping only the second source stops the same actual mixed angle,
with its changed-domain proof constructed and the original initial product retained. -/
theorem predictableQuadraticCovariation_stoppedProcess_right
    (hX : IsSemimartingale X F P) (hY : IsSemimartingale Y F P) (hF : F.IsUsual P)
    (hQ : HasLocallyIntegrableVariation (hX.quadraticCovariation hY hF) F P)
    (hτ : IsStoppingTime F τ) :
    let hQτ : HasLocallyIntegrableVariation
        (hX.quadraticCovariation (hY.stoppedProcess hF hτ) hF) F P :=
      (hQ.stoppedProcess (hX.adapted_quadraticCovariation hY hF) hF
        (hX.hasCadlagPaths_quadraticCovariation hY hF) hτ).congr
          (hX.quadraticCovariation_stoppedProcess_right hY hF hτ).symm
    Indistinguishable
      (hX.predictableQuadraticCovariation (hY.stoppedProcess hF hτ) hF hQτ)
      (MeasureTheory.stoppedProcess (hX.predictableQuadraticCovariation hY hF hQ) τ) P := by
  let hSY := hY.stoppedProcess hF hτ
  have hs := hQ.stoppedProcess (hX.adapted_quadraticCovariation hY hF) hF
    (hX.hasCadlagPaths_quadraticCovariation hY hF) hτ
  let hQτ := hs.congr (hX.quadraticCovariation_stoppedProcess_right hY hF hτ).symm
  have he := hQτ.predictableCompensator_congr hs (hX.adapted_quadraticCovariation hSY hF)
    ((hX.adapted_quadraticCovariation hY hF).stronglyAdapted.stoppedProcess_of_usual hF
      (hX.hasCadlagPaths_quadraticCovariation hY hF).hasRightContinuousPaths hτ).adapted hF
    (hX.hasCadlagPaths_quadraticCovariation hSY hF)
    ((hX.hasCadlagPaths_quadraticCovariation hY hF).stoppedProcess τ)
    (hX.quadraticCovariation_stoppedProcess_right hY hF hτ)
  exact he.trans (hQ.predictableCompensator_stoppedProcess
    (hX.adapted_quadraticCovariation hY hF) hF
    (hX.hasCadlagPaths_quadraticCovariation hY hF) hτ)

end ProbabilityTheory.IsSemimartingale
