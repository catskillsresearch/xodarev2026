/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.Semimartingale.PredictableQuadraticVariation
public import StochLean.Probability.Process.Semimartingale.QuadraticCovariation.Algebra

/-! # Predictable quadratic covariation on its actual domain

The mixed angle process is the existing canonical predictable compensator
of the actual raw quadratic covariation, guarded by locally integrable
variation of that process. No separate selection method is introduced.
The raw initial value is `X 0 * Y 0` almost surely, whereas its predictable
compensator starts exactly at zero. Initial moments are not assumed.

Unlike predictable quadratic variation, mixed predictable covariation need
not be increasing. Its predictable FV uniqueness, symmetry, and diagonal
agreement with the existing angle-square owner follow from the established
canonical compensator and the actual raw-covariation identities. Local L2
domain criteria and polarization of the angle processes are separate results.
-/

@[expose] public section

open MeasureTheory
open scoped NNReal

namespace ProbabilityTheory.IsSemimartingale

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
  {F : Filtration ℝ≥0 mΩ} {X Y : ℝ≥0 → Ω → ℝ}

/-- The mixed angle process is the sole canonical compensator applied to
actual raw covariation on its proved locally-integrable-variation domain. -/
noncomputable def predictableQuadraticCovariation
    (hX : IsSemimartingale X F P) (hY : IsSemimartingale Y F P) (hF : F.IsUsual P)
    (hQ : HasLocallyIntegrableVariation (hX.quadraticCovariation hY hF) F P) :
    ℝ≥0 → Ω → ℝ :=
  hQ.predictableCompensator (hX.adapted_quadraticCovariation hY hF) hF
    (hX.hasCadlagPaths_quadraticCovariation hY hF)

/-- The selected mixed angle has exact initial zero and an actual raw-minus-
angle local-martingale remainder. No monotonicity is asserted for a mixed pair. -/
theorem predictableQuadraticCovariation_properties
    (hX : IsSemimartingale X F P) (hY : IsSemimartingale Y F P) (hF : F.IsUsual P)
    (hQ : HasLocallyIntegrableVariation (hX.quadraticCovariation hY hF) F P) :
    let A := hX.predictableQuadraticCovariation hY hF hQ
    IsStronglyPredictable F A ∧ (∀ ω, IsCadlagPath (A · ω)) ∧ A 0 = 0 ∧
      HasLocallyIntegrableVariation A F P ∧
      IsLocalMartingale (hX.quadraticCovariation hY hF - A) F P :=
  hQ.predictableCompensator_properties (hX.adapted_quadraticCovariation hY hF) hF
    (hX.hasCadlagPaths_quadraticCovariation hY hF)

/-- Uniqueness holds among all normalized predictable FV competitors, not
only among selected angle processes or competitors assumed locally IV. -/
theorem predictableQuadraticCovariation_unique
    (hX : IsSemimartingale X F P) (hY : IsSemimartingale Y F P) (hF : F.IsUsual P)
    (hQ : HasLocallyIntegrableVariation (hX.quadraticCovariation hY hF) F P)
    {B : ℝ≥0 → Ω → ℝ} (hpB : IsStronglyPredictable F B)
    (hvB : HasFiniteVariationPaths B P) (hB0 : B 0 =ᵐ[P] 0)
    (hM : IsLocalMartingale (hX.quadraticCovariation hY hF - B) F P) :
    Indistinguishable (hX.predictableQuadraticCovariation hY hF hQ) B P :=
  hQ.predictableCompensator_unique (hX.adapted_quadraticCovariation hY hF) hF
    (hX.hasCadlagPaths_quadraticCovariation hY hF) hpB hvB hB0 hM

/-- Symmetry comes from the existing raw-covariation symmetry and canonical
compensator invariance. Both domain proofs concern the actual raw processes. -/
theorem predictableQuadraticCovariation_comm
    (hX : IsSemimartingale X F P) (hY : IsSemimartingale Y F P) (hF : F.IsUsual P)
    (hQXY : HasLocallyIntegrableVariation (hX.quadraticCovariation hY hF) F P)
    (hQYX : HasLocallyIntegrableVariation (hY.quadraticCovariation hX hF) F P) :
    Indistinguishable (hX.predictableQuadraticCovariation hY hF hQXY)
      (hY.predictableQuadraticCovariation hX hF hQYX) P :=
  hQXY.predictableCompensator_congr hQYX (hX.adapted_quadraticCovariation hY hF)
    (hY.adapted_quadraticCovariation hX hF) hF (hX.hasCadlagPaths_quadraticCovariation hY hF)
    (hY.hasCadlagPaths_quadraticCovariation hX hF) (hX.quadraticCovariation_comm hY hF)

/-- The diagonal mixed angle agrees with the existing predictable quadratic
variation, with each actual raw process carrying its own domain proof. -/
theorem predictableQuadraticCovariation_self
    (hX : IsSemimartingale X F P) (hF : F.IsUsual P)
    (hQ : HasLocallyIntegrableVariation (hX.quadraticCovariation hX hF) F P)
    (hV : HasLocallyIntegrableVariation (hX.quadraticVariation hF) F P) :
    Indistinguishable (hX.predictableQuadraticCovariation hX hF hQ)
      (hX.predictableQuadraticVariation hF hV) P :=
  hQ.predictableCompensator_congr hV (hX.adapted_quadraticCovariation hX hF)
    (hX.adapted_quadraticVariation hF) hF (hX.hasCadlagPaths_quadraticCovariation hX hF)
    (hX.hasCadlagPaths_quadraticVariation hF) (hX.quadraticCovariation_self hF)

end ProbabilityTheory.IsSemimartingale
