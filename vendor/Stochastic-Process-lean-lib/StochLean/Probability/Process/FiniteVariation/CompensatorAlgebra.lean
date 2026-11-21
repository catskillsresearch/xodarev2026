/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.FiniteVariation.CanonicalCompensator
public import StochLean.Probability.Process.FiniteVariation.LocallyIntegrableScaling

/-! # Linearity of the actual canonical predictable compensator

Addition, subtraction and real scaling preserve the actual legal domain.
The selected compensator agrees, on one common path event, with the same
operation on the original selected compensators. Full predictable-FV
uniqueness and actual local-martingale arithmetic prove these identities.
No integrability of original initial values or second selector is introduced.
-/

@[expose] public section

open MeasureTheory Filter
open scoped NNReal

namespace ProbabilityTheory.HasLocallyIntegrableVariation

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
  {F : Filtration ℝ≥0 mΩ} {X Y : ℝ≥0 → Ω → ℝ}

/-- The actual compensator of a sum is the sum of the actual compensators. -/
theorem predictableCompensator_add
    (hvX : HasLocallyIntegrableVariation X F P) (hvY : HasLocallyIntegrableVariation Y F P)
    (haX : Adapted F X) (haY : Adapted F Y) (hF : F.IsUsual P)
    (hcX : HasCadlagPaths X P) (hcY : HasCadlagPaths Y P) :
    Indistinguishable
      ((hvX.add hvY haX haY hF hcX hcY).predictableCompensator
        (haX.add haY) hF (hcX.add hcY))
      (hvX.predictableCompensator haX hF hcX + hvY.predictableCompensator haY hF hcY) P := by
  obtain ⟨hpA, hcA, hA0, hvA, hM⟩ := hvX.predictableCompensator_properties haX hF hcX
  obtain ⟨hpB, hcB, hB0, hvB, hN⟩ := hvY.predictableCompensator_properties haY hF hcY
  have hp : IsStronglyPredictable F
      (hvX.predictableCompensator haX hF hcX + hvY.predictableCompensator haY hF hcY) :=
    hpA.add hpB
  have hv := hvA.add hvB hpA.stronglyAdapted.adapted hpB.stronglyAdapted.adapted hF
    (Eventually.of_forall hcA) (Eventually.of_forall hcB)
  apply (hvX.add hvY haX haY hF hcX hcY).predictableCompensator_unique
    (haX.add haY) hF (hcX.add hcY) hp hv.hasFiniteVariationPaths
  · exact Eventually.of_forall fun ω ↦ by simp only [Pi.add_apply, hA0, hB0, Pi.zero_apply,
      add_zero]
  · apply (hM.add hN hF).congr hF ((haX.add haY).sub hp.stronglyAdapted.adapted)
    exact Eventually.of_forall fun ω t ↦ by
      simp only [Pi.sub_apply, Pi.add_apply]
      ring

/-- Real scaling includes zero and does not require an initial moment. -/
theorem predictableCompensator_smul
    (hvX : HasLocallyIntegrableVariation X F P) (haX : Adapted F X) (hF : F.IsUsual P)
    (hcX : HasCadlagPaths X P) (c : ℝ) :
    Indistinguishable
      ((hvX.smul c).predictableCompensator (fun t ↦ (haX t).const_smul c) hF
        (hcX.continuous_comp (continuous_const.mul continuous_id)))
      (c • hvX.predictableCompensator haX hF hcX) P := by
  obtain ⟨hpA, _, hA0, hvA, hM⟩ := hvX.predictableCompensator_properties haX hF hcX
  have hp : IsStronglyPredictable F (c • hvX.predictableCompensator haX hF hcX) :=
    hpA.const_smul c
  have ha : Adapted F (c • X) := fun t ↦ (haX t).const_smul c
  have hc : HasCadlagPaths (c • X) P :=
    hcX.continuous_comp (continuous_const.mul continuous_id)
  apply (hvX.smul c).predictableCompensator_unique ha hF hc hp
    (hvA.smul c).hasFiniteVariationPaths
  · exact Eventually.of_forall fun ω ↦ by
      simp only [Pi.smul_apply, hA0, Pi.zero_apply, smul_zero]
  · apply (hM.const_smul c).congr hF (ha.sub hp.stronglyAdapted.adapted)
    exact Eventually.of_forall fun ω t ↦ by
      simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
      ring

/-- Subtraction is an identity of selected processes on the actual domain. -/
theorem predictableCompensator_sub
    (hvX : HasLocallyIntegrableVariation X F P) (hvY : HasLocallyIntegrableVariation Y F P)
    (haX : Adapted F X) (haY : Adapted F Y) (hF : F.IsUsual P)
    (hcX : HasCadlagPaths X P) (hcY : HasCadlagPaths Y P) :
    Indistinguishable
      ((hvX.sub hvY haX haY hF hcX hcY).predictableCompensator
        (haX.sub haY) hF (hcX.sub hcY))
      (hvX.predictableCompensator haX hF hcX - hvY.predictableCompensator haY hF hcY) P := by
  obtain ⟨hpA, hcA, hA0, hvA, hM⟩ := hvX.predictableCompensator_properties haX hF hcX
  obtain ⟨hpB, hcB, hB0, hvB, hN⟩ := hvY.predictableCompensator_properties haY hF hcY
  have hp : IsStronglyPredictable F
      (hvX.predictableCompensator haX hF hcX - hvY.predictableCompensator haY hF hcY) :=
    hpA.sub hpB
  have hv := hvA.sub hvB hpA.stronglyAdapted.adapted hpB.stronglyAdapted.adapted hF
    (Eventually.of_forall hcA) (Eventually.of_forall hcB)
  apply (hvX.sub hvY haX haY hF hcX hcY).predictableCompensator_unique
    (haX.sub haY) hF (hcX.sub hcY) hp hv.hasFiniteVariationPaths
  · exact Eventually.of_forall fun ω ↦ by
      simp only [Pi.sub_apply, hA0, hB0, Pi.zero_apply, sub_zero]
  · apply (hM.sub hN hF).congr hF ((haX.sub haY).sub hp.stronglyAdapted.adapted)
    exact Eventually.of_forall fun ω t ↦ by
      simp only [Pi.sub_apply]
      ring

end ProbabilityTheory.HasLocallyIntegrableVariation
