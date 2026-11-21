/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.FiniteVariation.CompensatorLocalMonotone
public import StochLean.Probability.Process.Semimartingale.SpecialIntegrableVariation

/-! # The canonical predictable compensator on its proved domain

The already proved existence and uniqueness theorem now supplies the sole
continuous-time compensator selector. It is guarded by actual locally
integrable variation, adaptedness, cadlag paths and the usual conditions.
There is no value outside this mathematical domain.

Uniqueness is against arbitrary predictable FV competitors, not just selected
ones. Indistinguishable inputs have indistinguishable compensators. The
selector agrees with the existing canonical FV part on the special domain,
so it is not a second competing canonical decomposition. Original initial
values need not be zero or integrable; the compensator starts exactly at zero.
-/

@[expose] public section

open MeasureTheory Filter
open scoped NNReal

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
  {F : Filtration ℝ≥0 mΩ} {X Y : ℝ≥0 → Ω → ℝ}

/-- The unique normalized predictable compensator, selected only after
actual existence has been proved on the locally integrable-variation domain. -/
noncomputable def HasLocallyIntegrableVariation.predictableCompensator
    (hv : HasLocallyIntegrableVariation X F P) (ha : Adapted F X) (hF : F.IsUsual P)
    (hc : HasCadlagPaths X P) : ℝ≥0 → Ω → ℝ :=
  (hv.exists_unique_predictable_compensator ha hF hc).choose

/-- The selected raw compensator has all the properties of its actual
construction, including everywhere cadlag paths and exact initial zero. -/
theorem HasLocallyIntegrableVariation.predictableCompensator_properties
    (hv : HasLocallyIntegrableVariation X F P) (ha : Adapted F X) (hF : F.IsUsual P)
    (hc : HasCadlagPaths X P) :
    let A := hv.predictableCompensator ha hF hc
    IsStronglyPredictable F A ∧ (∀ ω, IsCadlagPath (A · ω)) ∧ A 0 = 0 ∧
      HasLocallyIntegrableVariation A F P ∧ IsLocalMartingale (X - A) F P := by
  obtain ⟨hp, hcA, h0, hvA, hM, _⟩ :=
    (hv.exists_unique_predictable_compensator ha hF hc).choose_spec
  exact ⟨hp, hcA, h0, hvA, hM⟩

/-- Uniqueness retains the full predictable FV competitor domain; local IV
of the competing part is a conclusion of the theory, not a new premise. -/
theorem HasLocallyIntegrableVariation.predictableCompensator_unique
    (hv : HasLocallyIntegrableVariation X F P) (ha : Adapted F X) (hF : F.IsUsual P)
    (hc : HasCadlagPaths X P) {B : ℝ≥0 → Ω → ℝ}
    (hpB : IsStronglyPredictable F B) (hvB : HasFiniteVariationPaths B P)
    (hB0 : B 0 =ᵐ[P] 0) (hM : IsLocalMartingale (X - B) F P) :
    Indistinguishable (hv.predictableCompensator ha hF hc) B P :=
  (hv.exists_unique_predictable_compensator ha hF hc).choose_spec.2.2.2.2.2
    B hpB hvB hB0 hM

/-- Common path equality of original sources preserves the selected
compensator, without imposing any common initial moment. -/
theorem HasLocallyIntegrableVariation.predictableCompensator_congr
    (hvX : HasLocallyIntegrableVariation X F P) (hvY : HasLocallyIntegrableVariation Y F P)
    (haX : Adapted F X) (haY : Adapted F Y) (hF : F.IsUsual P)
    (hcX : HasCadlagPaths X P) (hcY : HasCadlagPaths Y P)
    (he : Indistinguishable X Y P) :
    Indistinguishable (hvX.predictableCompensator haX hF hcX)
      (hvY.predictableCompensator haY hF hcY) P := by
  let A := hvX.predictableCompensator haX hF hcX
  obtain ⟨hpA, _, hA0, hvA, hM⟩ := hvX.predictableCompensator_properties haX hF hcX
  have hMY : IsLocalMartingale (Y - A) F P := by
    apply hM.congr hF (haY.sub hpA.stronglyAdapted.adapted)
    filter_upwards [he] with ω hω t
    change X t ω - A t ω = Y t ω - A t ω
    rw [hω t]
  exact (hvY.predictableCompensator_unique haY hF hcY hpA hvA.hasFiniteVariationPaths
    (Eventually.of_forall fun ω ↦ congrFun hA0 ω) hMY).symm

/-- Monotone sources have monotone selected compensators. -/
theorem HasLocallyIntegrableVariation.hasMonotonePaths_predictableCompensator
    (hv : HasLocallyIntegrableVariation X F P) (ha : Adapted F X) (hF : F.IsUsual P)
    (hc : HasCadlagPaths X P) (hm : HasMonotonePaths X P) :
    HasMonotonePaths (hv.predictableCompensator ha hF hc) P := by
  obtain ⟨hpA, _, hA0, hvA, hM⟩ := hv.predictableCompensator_properties ha hF hc
  exact hv.hasMonotonePaths_predictable_compensator ha hF hc hm hpA hvA
    (Eventually.of_forall fun ω ↦ congrFun hA0 ω) hM

/-- Actual compensation makes every adapted cadlag locally-IV process
special. The original random initial value is retained without a moment
assumption; only the normalized martingale component is centered. -/
theorem HasLocallyIntegrableVariation.isSpecialSemimartingale
    (hv : HasLocallyIntegrableVariation X F P) (ha : Adapted F X) (hF : F.IsUsual P)
    (hc : HasCadlagPaths X P) : IsSpecialSemimartingale X F P := by
  let A := hv.predictableCompensator ha hF hc
  let I : ℝ≥0 → Ω → ℝ := fun _ ↦ X 0
  let M := (X - A) - I
  obtain ⟨hpA, hcA, hA0, hvA, hU⟩ := hv.predictableCompensator_properties ha hF hc
  have hI : IsLocalMartingale I F P := (isContinuousLocalMartingale_const_initial (ha 0)).1
  have hM : IsLocalMartingale M F P := hU.sub hI hF
  refine ⟨ha, hc, M, A, hM, hpA, Eventually.of_forall hcA,
    hvA.hasFiniteVariationPaths, ?_, Eventually.of_forall (fun ω ↦ congrFun hA0 ω), ?_⟩
  · exact Eventually.of_forall fun ω ↦ by
      change (X 0 ω - A 0 ω) - X 0 ω = 0
      rw [show A 0 ω = 0 from congrFun hA0 ω, sub_zero, sub_self]
  · exact Eventually.of_forall fun ω t ↦ by
      change X t ω = (X 0 ω + ((X t ω - A t ω) - X 0 ω)) + A t ω
      ring

/-- The existing canonical special parts and the selected compensator are
coherent: the original process minus this compensator is the canonical
martingale, and the compensator is the canonical FV part. -/
theorem IsSpecialSemimartingale.canonicalParts_eq_predictableCompensator
    (hX : IsSpecialSemimartingale X F P) (hF : F.IsUsual P)
    (hv : HasLocallyIntegrableVariation X F P) :
    let A := hv.predictableCompensator hX.1 hF hX.2.1
    Indistinguishable hX.canonicalMartingalePart (X - A) P ∧
      Indistinguishable hX.canonicalFiniteVariationPart A P := by
  obtain ⟨hpA, _, hA0, hvA, hM⟩ := hv.predictableCompensator_properties hX.1 hF hX.2.1
  apply hX.canonicalDecomposition_unique hF hM hpA hvA.hasFiniteVariationPaths
    (Eventually.of_forall fun ω ↦ congrFun hA0 ω)
  exact Eventually.of_forall fun ω t ↦ (sub_add_cancel (X t ω) _).symm

end ProbabilityTheory
