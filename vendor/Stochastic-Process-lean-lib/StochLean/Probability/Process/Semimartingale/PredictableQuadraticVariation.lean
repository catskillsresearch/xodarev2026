/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.FiniteVariation.CanonicalCompensator
public import StochLean.Probability.Process.FiniteVariation.MonotoneLocalIntegrability
public import StochLean.Probability.Process.Semimartingale.QuadraticVariation.Increasing

/-! # Predictable quadratic variation on its proved domain

The continuous-time angle process is the existing canonical predictable
compensator of the actual raw quadratic variation. It is selected only after
locally integrable variation of that raw process has been established. Native
local coordinate integrability supplies this domain condition because the raw
quadratic variation is genuinely increasing.

The ordinary and predictable quadratic variations remain distinct: the raw
process has initial value `X 0 ^ 2` almost surely, while its compensator starts
exactly at zero. The difference is a Protter local martingale; the original
initial square is not discarded or assumed integrable. Uniqueness applies to
all normalized predictable FV competitors, and common path changes preserve
the selected angle process. No second compensator selector is introduced.
-/

@[expose] public section

open MeasureTheory
open scoped NNReal

namespace ProbabilityTheory.IsSemimartingale

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
  {F : Filtration ℝ≥0 mΩ} {X Y : ℝ≥0 → Ω → ℝ}

/-- The continuous-time predictable quadratic variation is the actual
canonical compensator of raw quadratic variation on its legal domain. -/
noncomputable def predictableQuadraticVariation
    (hX : IsSemimartingale X F P) (hF : F.IsUsual P)
    (hQ : HasLocallyIntegrableVariation (hX.quadraticVariation hF) F P) : ℝ≥0 → Ω → ℝ :=
  hQ.predictableCompensator (hX.adapted_quadraticVariation hF) hF
    (hX.hasCadlagPaths_quadraticVariation hF)

/-- All properties refer to the selected angle process itself. Its monotonicity
comes from the actual increasing raw quadratic variation. -/
theorem predictableQuadraticVariation_properties
    (hX : IsSemimartingale X F P) (hF : F.IsUsual P)
    (hQ : HasLocallyIntegrableVariation (hX.quadraticVariation hF) F P) :
    let A := hX.predictableQuadraticVariation hF hQ
    IsStronglyPredictable F A ∧ (∀ ω, IsCadlagPath (A · ω)) ∧ A 0 = 0 ∧
      HasMonotonePaths A P ∧ HasLocallyIntegrableVariation A F P ∧
      IsLocalMartingale (hX.quadraticVariation hF - A) F P := by
  obtain ⟨hp, hc, h0, hv, hM⟩ := hQ.predictableCompensator_properties
    (hX.adapted_quadraticVariation hF) hF (hX.hasCadlagPaths_quadraticVariation hF)
  have hm := hQ.hasMonotonePaths_predictableCompensator
    (hX.adapted_quadraticVariation hF) hF (hX.hasCadlagPaths_quadraticVariation hF)
    (hX.hasMonotonePaths_quadraticVariation hF)
  exact ⟨hp, hc, h0, hm, hv, hM⟩

/-- The angle process is unique among all predictable FV processes with
almost-sure zero initial value and the stated local-martingale remainder.
No additional cadlag or local-integrability premise is imposed on a competitor. -/
theorem predictableQuadraticVariation_unique
    (hX : IsSemimartingale X F P) (hF : F.IsUsual P)
    (hQ : HasLocallyIntegrableVariation (hX.quadraticVariation hF) F P)
    {B : ℝ≥0 → Ω → ℝ} (hpB : IsStronglyPredictable F B)
    (hvB : HasFiniteVariationPaths B P) (hB0 : B 0 =ᵐ[P] 0)
    (hM : IsLocalMartingale (hX.quadraticVariation hF - B) F P) :
    Indistinguishable (hX.predictableQuadraticVariation hF hQ) B P :=
  hQ.predictableCompensator_unique (hX.adapted_quadraticVariation hF) hF
    (hX.hasCadlagPaths_quadraticVariation hF) hpB hvB hB0 hM

/-- Native local integrability of the original raw quadratic variation gives
the actual domain proof and the selected predictable quadratic variation.
No candidate angle process or compensator is an input. -/
theorem exists_predictableQuadraticVariation_of_locally_integrable
    (hX : IsSemimartingale X F P) (hF : F.IsUsual P)
    (hL : Locally (fun Z : ℝ≥0 → Ω → ℝ ↦ ∀ t, Integrable (Z t) P) F
      (hX.quadraticVariation hF) P) :
    ∃ hQ : HasLocallyIntegrableVariation (hX.quadraticVariation hF) F P,
      let A := hX.predictableQuadraticVariation hF hQ
      IsStronglyPredictable F A ∧ (∀ ω, IsCadlagPath (A · ω)) ∧ A 0 = 0 ∧
        HasMonotonePaths A P ∧ HasLocallyIntegrableVariation A F P ∧
        IsLocalMartingale (hX.quadraticVariation hF - A) F P := by
  have hQ := HasMonotonePaths.hasLocallyIntegrableVariation_of_locally_integrable
    (hX.hasMonotonePaths_quadraticVariation hF) (hX.adapted_quadraticVariation hF) hF
    (hX.hasCadlagPaths_quadraticVariation hF) hL
  exact ⟨hQ, hX.predictableQuadraticVariation_properties hF hQ⟩

/-- Indistinguishable source processes have indistinguishable selected angle
processes. Both domain proofs concern their own actual raw quadratic variation. -/
theorem predictableQuadraticVariation_congr
    (hX : IsSemimartingale X F P) (hY : IsSemimartingale Y F P) (hF : F.IsUsual P)
    (hQX : HasLocallyIntegrableVariation (hX.quadraticVariation hF) F P)
    (hQY : HasLocallyIntegrableVariation (hY.quadraticVariation hF) F P)
    (he : Indistinguishable X Y P) :
    Indistinguishable (hX.predictableQuadraticVariation hF hQX)
      (hY.predictableQuadraticVariation hF hQY) P :=
  hQX.predictableCompensator_congr hQY (hX.adapted_quadraticVariation hF)
    (hY.adapted_quadraticVariation hF) hF (hX.hasCadlagPaths_quadraticVariation hF)
    (hY.hasCadlagPaths_quadraticVariation hF) (hX.quadraticVariation_congr hY hF he)

end ProbabilityTheory.IsSemimartingale
