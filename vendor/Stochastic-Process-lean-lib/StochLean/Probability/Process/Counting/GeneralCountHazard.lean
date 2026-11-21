/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.Counting.ArrivalCountVersion
public import StochLean.Probability.Process.Counting.NaturalCompensatorDomain
public import StochLean.Probability.Process.Counting.ArrivalHazardCompensatorInterval
public import StochLean.Probability.Process.Filtration.NaturalIndistinguishable

/-! # Conditional-arrival hazards for an almost-sure counting process

An actual nonexplosive count has an everywhere-valid measurable arrival
representative through the existing common-null-set construction. Its count
is indistinguishable from the original count and its arrivals agree with
the original hitting times on one common event.

The genuine usual natural filtrations of the two counts are equal. Canonical
compensator congruence therefore transports the conditional-gap formula to
the original count, with the original count itself choosing the completed
and pending indices. Conditional kernels are computed only under the original
measure, using actual gaps of the legitimate representative.

The supplied usual filtration is used to construct that representative; the
final formula is in the original count's usual natural augmentation, not
in an arbitrary information enlargement. There is no initial or total-count
moment assumption and no candidate compensator input.
-/

@[expose] public section

open MeasureTheory Filter Set
open scoped NNReal ENNReal

namespace ProbabilityTheory.IsNonexplosiveCountingProcess

private theorem compensator_congr_of_filtration_eq
    {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
    {G G' : Filtration ℝ≥0 mΩ} {U V : ℝ≥0 → Ω → ℝ}
    (hEq : G = G')
    (hvU : HasLocallyIntegrableVariation U G P)
    (hvV : HasLocallyIntegrableVariation V G' P)
    (haU : Adapted G U) (haV : Adapted G' V)
    (hG : G.IsUsual P) (hG' : G'.IsUsual P)
    (hcU : HasCadlagPaths U P) (hcV : HasCadlagPaths V P)
    (he : Indistinguishable U V P) :
    Indistinguishable (hvU.predictableCompensator haU hG hcU)
      (hvV.predictableCompensator haV hG' hcV) P := by
  cases hEq
  exact hvU.predictableCompensator_congr hvV haU haV hG hcU hcV he

/-- An actual almost-sure count has a legitimate arrival representative
whose original conditional-gap hazards give the original count's canonical
compensator in its genuine usual natural filtration. The finite formula
uses the original count index and retains common-event hitting-time agreement. -/
theorem exists_arrivalSequence_predictableCompensator_eq_hazard
    {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
    {F : Filtration ℝ≥0 mΩ} {N : ℝ≥0 → Ω → ℕ}
    (hN : IsNonexplosiveCountingProcess N P) (ha : Adapted F N) (hF : F.IsUsual P) :
    let : StandardBorelSpace (WithTop ℝ≥0) := inferInstanceAs (StandardBorelSpace ℝ≥0∞)
    let hMeasN : ∀ t, Measurable (N t) := fun t ↦ ha.measurable (i := t)
    let FN := Filtration.natural N (fun t ↦ (hMeasN t).stronglyMeasurable)
    let hD := hN.natural_usual_compensator_domain hMeasN
    ∃ Γ : ℕ → Ω → WithTop ℝ≥0,
      ∃ hΓ : ∀ ω, IsNonexplosiveArrivalSequence (fun n ↦ Γ n ω),
        (∀ n, Measurable (Γ n)) ∧
        Indistinguishable (fun t ω ↦ (hΓ ω).count t) N P ∧
        (∀ᵐ ω ∂P, ∀ n, Γ n ω = hittingAfter N (Ioi n) 0 ω) ∧
        let G := fun (n : ℕ) (ω : Ω) (i : Fin n) ↦
          arrivalInterarrival (fun j ↦ Γ j ω) i
        let L := fun n ↦
          Nat.casesOn (motive := fun _ ↦ Ω → WithTop ℝ≥0) n (fun _ ↦ 0) Γ
        let S := fun (n : ℕ) (ω : Ω) ↦ arrivalInterarrival (fun j ↦ Γ j ω) n
        let κ := fun n ↦ condDistrib (S n) (G n) P
        Indistinguishable
          (hD.2.2.predictableCompensator hD.1 (FN.usualAugmentation_isUsual P) hD.2.1)
          (fun (t : ℝ≥0) (ω : NullMeasurableSpace Ω P) ↦
            let k := N t ω
            (∑ n ∈ Finset.range k,
              (eCumulativeHazard (κ n (G n ω)) (S n ω).untopA).toReal) +
            (eCumulativeHazard (κ k (G k ω)) (t - (L k ω).untopA)).toReal)
          P.completion := by
  let : StandardBorelSpace (WithTop ℝ≥0) := inferInstanceAs (StandardBorelSpace ℝ≥0∞)
  obtain ⟨Γ, hΓ, hMeasΓ, _, he, hhits⟩ := hN.exists_arrivalSequence_count_version ha hF
  refine ⟨Γ, hΓ, hMeasΓ, he, hhits, ?_⟩
  let hMeasN : ∀ t, Measurable (N t) := fun t ↦ ha.measurable (i := t)
  let FN := Filtration.natural N (fun t ↦ (hMeasN t).stronglyMeasurable)
  let hMeasR := fun t ↦
    (IsNonexplosiveArrivalSequence.measurable_count hΓ hMeasΓ t).stronglyMeasurable
  let FR := Filtration.natural (fun t ω ↦ (hΓ ω).count t) hMeasR
  have hFil : FN.usualAugmentation P = FR.usualAugmentation P :=
    Filtration.natural_usualAugmentation_eq_of_indistinguishable
      (fun t ↦ (hMeasN t).stronglyMeasurable) hMeasR he.symm
  let C := fun (t : ℝ≥0) (ω : NullMeasurableSpace Ω P) ↦ (N t ω : ℝ)
  let R := fun (t : ℝ≥0) (ω : NullMeasurableSpace Ω P) ↦ ((hΓ ω).count t : ℝ)
  have hCR : Indistinguishable C R P.completion := by
    filter_upwards [he] with ω hω t
    exact congrArg (fun k : ℕ ↦ (k : ℝ)) (hω t).symm
  have hD := hN.natural_usual_compensator_domain hMeasN
  have hR := IsNonexplosiveArrivalSequence.count_compensator_domain_natural_usual
    (P := P) hΓ hMeasΓ
  have hComp := compensator_congr_of_filtration_eq hFil hD.2.2 hR.2.2 hD.1 hR.1
    (FN.usualAugmentation_isUsual P) (FR.usualAugmentation_isUsual P)
    hD.2.1 hR.2.1 hCR
  have hFormula :=
    IsNonexplosiveArrivalSequence.predictableCompensator_count_eq_completed_add_pending_hazard
      (P := P) hΓ hMeasΓ
  refine hComp.trans (hFormula.trans ?_)
  filter_upwards [he] with ω hω t
  dsimp only
  rw [hω t]

end ProbabilityTheory.IsNonexplosiveCountingProcess
