/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.Semimartingale.PredictableQuadraticCovariation
public import StochLean.Probability.Process.FiniteVariation.CompensatorAlgebra

/-! # Bilinearity of the actual mixed angle process

The legal domains for added or real-scaled sources are derived from the
original raw-covariation domains by actual local-IV algebra and the proved
raw identities. No transformed-domain conclusion is assumed as a premise.
The sole canonical compensator's linearity and version invariance then
identify the already selected mixed angles on one common path event.

Scalars may have either sign or be zero. Mixed angles are not asserted to
be increasing, and no local L2 or initial-moment assumption is introduced.
-/

@[expose] public section

open MeasureTheory
open scoped NNReal

namespace ProbabilityTheory.IsSemimartingale

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
  {F : Filtration ℝ≥0 mΩ} {X Y Z X' Y' : ℝ≥0 → Ω → ℝ}

/-- Addition in the first source, with the actual sum-domain guard derived
from the two original raw mixed domains. -/
theorem predictableQuadraticCovariation_add_left
    (hX : IsSemimartingale X F P) (hY : IsSemimartingale Y F P)
    (hZ : IsSemimartingale Z F P) (hF : F.IsUsual P)
    (hQXZ : HasLocallyIntegrableVariation (hX.quadraticCovariation hZ hF) F P)
    (hQYZ : HasLocallyIntegrableVariation (hY.quadraticCovariation hZ hF) F P) :
    let hQS : HasLocallyIntegrableVariation ((hX.add hY).quadraticCovariation hZ hF) F P :=
      (hQXZ.add hQYZ (hX.adapted_quadraticCovariation hZ hF)
        (hY.adapted_quadraticCovariation hZ hF) hF
        (hX.hasCadlagPaths_quadraticCovariation hZ hF)
        (hY.hasCadlagPaths_quadraticCovariation hZ hF)).congr
        (hX.quadraticCovariation_add_left hY hZ hF).symm
    Indistinguishable ((hX.add hY).predictableQuadraticCovariation hZ hF hQS)
      (hX.predictableQuadraticCovariation hZ hF hQXZ +
        hY.predictableQuadraticCovariation hZ hF hQYZ) P := by
  have haX := hX.adapted_quadraticCovariation hZ hF
  have haY := hY.adapted_quadraticCovariation hZ hF
  have hcX := hX.hasCadlagPaths_quadraticCovariation hZ hF
  have hcY := hY.hasCadlagPaths_quadraticCovariation hZ hF
  let hvSum := hQXZ.add hQYZ haX haY hF hcX hcY
  let hQS := hvSum.congr (hX.quadraticCovariation_add_left hY hZ hF).symm
  exact (hQS.predictableCompensator_congr hvSum
    ((hX.add hY).adapted_quadraticCovariation hZ hF) (haX.add haY) hF
    ((hX.add hY).hasCadlagPaths_quadraticCovariation hZ hF) (hcX.add hcY)
    (hX.quadraticCovariation_add_left hY hZ hF)).trans
    (hQXZ.predictableCompensator_add hQYZ haX haY hF hcX hcY)

/-- Addition in the second source uses the actual right-add raw identity
and derives its legal domain from the two supplied original domains. -/
theorem predictableQuadraticCovariation_add_right
    (hX : IsSemimartingale X F P) (hY : IsSemimartingale Y F P)
    (hZ : IsSemimartingale Z F P) (hF : F.IsUsual P)
    (hQXY : HasLocallyIntegrableVariation (hX.quadraticCovariation hY hF) F P)
    (hQXZ : HasLocallyIntegrableVariation (hX.quadraticCovariation hZ hF) F P) :
    let hQS : HasLocallyIntegrableVariation (hX.quadraticCovariation (hY.add hZ) hF) F P :=
      (hQXY.add hQXZ (hX.adapted_quadraticCovariation hY hF)
        (hX.adapted_quadraticCovariation hZ hF) hF
        (hX.hasCadlagPaths_quadraticCovariation hY hF)
        (hX.hasCadlagPaths_quadraticCovariation hZ hF)).congr
        (hX.quadraticCovariation_add_right hY hZ hF).symm
    Indistinguishable (hX.predictableQuadraticCovariation (hY.add hZ) hF hQS)
      (hX.predictableQuadraticCovariation hY hF hQXY +
        hX.predictableQuadraticCovariation hZ hF hQXZ) P := by
  have haY := hX.adapted_quadraticCovariation hY hF
  have haZ := hX.adapted_quadraticCovariation hZ hF
  have hcY := hX.hasCadlagPaths_quadraticCovariation hY hF
  have hcZ := hX.hasCadlagPaths_quadraticCovariation hZ hF
  let hvSum := hQXY.add hQXZ haY haZ hF hcY hcZ
  let hQS := hvSum.congr (hX.quadraticCovariation_add_right hY hZ hF).symm
  exact (hQS.predictableCompensator_congr hvSum
    (hX.adapted_quadraticCovariation (hY.add hZ) hF) (haY.add haZ) hF
    (hX.hasCadlagPaths_quadraticCovariation (hY.add hZ) hF) (hcY.add hcZ)
    (hX.quadraticCovariation_add_right hY hZ hF)).trans
    (hQXY.predictableCompensator_add hQXZ haY haZ hF hcY hcZ)

/-- Real scaling in the first source includes negative and zero scalars.
Local IV of the transformed raw process is constructed from the original. -/
theorem predictableQuadraticCovariation_const_mul_left
    (hX : IsSemimartingale X F P) (hY : IsSemimartingale Y F P) (hF : F.IsUsual P)
    (hQ : HasLocallyIntegrableVariation (hX.quadraticCovariation hY hF) F P) (c : ℝ) :
    let hQC : HasLocallyIntegrableVariation ((hX.const_mul c).quadraticCovariation hY hF) F P :=
      (hQ.smul c).congr (hX.quadraticCovariation_const_mul_left hY hF c).symm
    Indistinguishable ((hX.const_mul c).predictableQuadraticCovariation hY hF hQC)
      (c • hX.predictableQuadraticCovariation hY hF hQ) P := by
  have ha := hX.adapted_quadraticCovariation hY hF
  have hc := hX.hasCadlagPaths_quadraticCovariation hY hF
  have haC : Adapted F (c • hX.quadraticCovariation hY hF) :=
    fun t ↦ (ha t).const_smul c
  have hcC : HasCadlagPaths (c • hX.quadraticCovariation hY hF) P :=
    hc.continuous_comp (continuous_const.mul continuous_id)
  let hQC := (hQ.smul c).congr (hX.quadraticCovariation_const_mul_left hY hF c).symm
  exact (hQC.predictableCompensator_congr (hQ.smul c)
    ((hX.const_mul c).adapted_quadraticCovariation hY hF) haC hF
    ((hX.const_mul c).hasCadlagPaths_quadraticCovariation hY hF) hcC
    (hX.quadraticCovariation_const_mul_left hY hF c)).trans
    (hQ.predictableCompensator_smul ha hF hc c)

/-- Real scaling in the second source has the same actual-domain guarantee;
the assertion is an equality of selected processes, not a new selection rule. -/
theorem predictableQuadraticCovariation_const_mul_right
    (hX : IsSemimartingale X F P) (hY : IsSemimartingale Y F P) (hF : F.IsUsual P)
    (hQ : HasLocallyIntegrableVariation (hX.quadraticCovariation hY hF) F P) (c : ℝ) :
    let hQC : HasLocallyIntegrableVariation (hX.quadraticCovariation (hY.const_mul c) hF) F P :=
      (hQ.smul c).congr (hX.quadraticCovariation_const_mul_right hY hF c).symm
    Indistinguishable (hX.predictableQuadraticCovariation (hY.const_mul c) hF hQC)
      (c • hX.predictableQuadraticCovariation hY hF hQ) P := by
  have ha := hX.adapted_quadraticCovariation hY hF
  have hc := hX.hasCadlagPaths_quadraticCovariation hY hF
  have haC : Adapted F (c • hX.quadraticCovariation hY hF) :=
    fun t ↦ (ha t).const_smul c
  have hcC : HasCadlagPaths (c • hX.quadraticCovariation hY hF) P :=
    hc.continuous_comp (continuous_const.mul continuous_id)
  let hQC := (hQ.smul c).congr (hX.quadraticCovariation_const_mul_right hY hF c).symm
  exact (hQC.predictableCompensator_congr (hQ.smul c)
    (hX.adapted_quadraticCovariation (hY.const_mul c) hF) haC hF
    (hX.hasCadlagPaths_quadraticCovariation (hY.const_mul c) hF) hcC
    (hX.quadraticCovariation_const_mul_right hY hF c)).trans
    (hQ.predictableCompensator_smul ha hF hc c)

/-- Common changes of both source paths preserve the actual selected mixed
angle. The two guards concern their own actual raw-covariation processes. -/
theorem predictableQuadraticCovariation_congr
    (hX : IsSemimartingale X F P) (hY : IsSemimartingale Y F P)
    (hX' : IsSemimartingale X' F P) (hY' : IsSemimartingale Y' F P) (hF : F.IsUsual P)
    (hQ : HasLocallyIntegrableVariation (hX.quadraticCovariation hY hF) F P)
    (hQ' : HasLocallyIntegrableVariation (hX'.quadraticCovariation hY' hF) F P)
    (hXX' : Indistinguishable X X' P) (hYY' : Indistinguishable Y Y' P) :
    Indistinguishable (hX.predictableQuadraticCovariation hY hF hQ)
      (hX'.predictableQuadraticCovariation hY' hF hQ') P :=
  hQ.predictableCompensator_congr hQ' (hX.adapted_quadraticCovariation hY hF)
    (hX'.adapted_quadraticCovariation hY' hF) hF (hX.hasCadlagPaths_quadraticCovariation hY hF)
    (hX'.hasCadlagPaths_quadraticCovariation hY' hF)
    (hX.quadraticCovariation_congr hY hX' hY' hF hXX' hYY')

end ProbabilityTheory.IsSemimartingale
