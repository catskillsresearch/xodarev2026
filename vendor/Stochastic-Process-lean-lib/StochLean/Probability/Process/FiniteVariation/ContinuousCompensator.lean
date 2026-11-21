/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.FiniteVariation.CompensatorPredictable
public import StochLean.Probability.Process.FiniteVariation.PredictableLocallyIntegrable
public import StochLean.Probability.Process.Measurability.Predictable

/-! # Actual compensators of AE-continuous finite-variation processes

An adapted AE-continuous FV process has locally integrable variation. The
existing predictable version gives that property, which transfers back to
the original process on a common path event. The actual canonical compensator
is the original process minus its original constant initial value, up to
indistinguishability. Exceptional original paths are not declared predictable,
and no initial integrability or zero-initial assumption is added.
-/

@[expose] public section

open MeasureTheory
open scoped NNReal

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
  {F : Filtration ℝ≥0 mΩ} {X : ℝ≥0 → Ω → ℝ}

private theorem exists_predictable_continuous_localIV_version
    (ha : Adapted F X) (hF : F.IsUsual P) (hc : HasContinuousPaths X P)
    (hv : HasFiniteVariationPaths X P) :
    ∃ Y : ℝ≥0 → Ω → ℝ, Indistinguishable X Y P ∧ IsStronglyPredictable F Y ∧
      HasContinuousPaths Y P ∧ HasLocallyIntegrableVariation Y F P := by
  obtain ⟨Y, he, hpY, _⟩ :=
    ha.exists_predictable_indistinguishable_of_hasLeftContinuousPaths hF hc.hasLeftContinuousPaths
  have hcY := HasContinuousPaths.congr he hc
  have hvY := HasFiniteVariationPaths.congr he hv
  exact ⟨Y, he, hpY, hcY, hpY.hasLocallyIntegrableVariation hF hcY.hasCadlagPaths hvY⟩

end ProbabilityTheory

namespace MeasureTheory.Adapted

open ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
  {F : Filtration ℝ≥0 mΩ} {X : ℝ≥0 → Ω → ℝ}

/-- An adapted AE-continuous FV process is actually locally integrable in
variation, without integrability of its original initial value. -/
theorem hasLocallyIntegrableVariation_of_continuous_finiteVariation
    (ha : Adapted F X) (hF : F.IsUsual P) (hc : HasContinuousPaths X P)
    (hv : HasFiniteVariationPaths X P) : HasLocallyIntegrableVariation X F P := by
  obtain ⟨_, he, _, _, hvY⟩ := exists_predictable_continuous_localIV_version ha hF hc hv
  exact hvY.congr he.symm

end MeasureTheory.Adapted

namespace ProbabilityTheory.HasLocallyIntegrableVariation

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
  {F : Filtration ℝ≥0 mΩ} {X : ℝ≥0 → Ω → ℝ}

/-- The actual compensator of an AE-continuous source is its centered
original process. Predictability is used only on an existing good version. -/
theorem predictableCompensator_eq_sub_initial_of_hasContinuousPaths
    (hv : HasLocallyIntegrableVariation X F P) (ha : Adapted F X) (hF : F.IsUsual P)
    (hc : HasContinuousPaths X P) :
    Indistinguishable (hv.predictableCompensator ha hF hc.hasCadlagPaths)
      (X - fun _ ↦ X 0) P := by
  obtain ⟨Y, he, hpY, hcY, hvY⟩ :=
    exists_predictable_continuous_localIV_version ha hF hc hv.hasFiniteVariationPaths
  have haY := hpY.stronglyAdapted.adapted
  have heComp := hv.predictableCompensator_congr hvY ha haY hF
    hc.hasCadlagPaths hcY.hasCadlagPaths he
  have heY := hvY.predictableCompensator_eq_sub_initial_of_predictable
    haY hF hcY.hasCadlagPaths hpY
  apply heComp.trans (heY.trans ?_)
  filter_upwards [he] with ω hω t
  change Y t ω - Y 0 ω = X t ω - X 0 ω
  rw [← hω t, ← hω 0]

end ProbabilityTheory.HasLocallyIntegrableVariation
