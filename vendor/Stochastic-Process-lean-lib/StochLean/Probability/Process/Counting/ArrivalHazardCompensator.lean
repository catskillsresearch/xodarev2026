/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.Counting.ArrivalHazardLocalization
public import StochLean.Probability.Process.Counting.Compensator

/-! # The sole compensator of the actual arrival count

Measurable nonexplosive arrivals construct the original count and its local
integrable-variation domain in the genuine usual natural augmentation. Its
conditional-hazard series is computed entirely from the original measure,
before augmentation. The proved local martingale remainder and predictable
finite-variation paths identify this series with the project's existing sole
canonical compensator, by the full uniqueness theorem.

No conditional kernel is recomputed after completion, no alternate
compensator is selected, and no finite expected total count is required.
The first arrival has index zero, the initial count is zero, and infinite
arrival tails remain allowed. This is the conditional-arrival-history form
of Protter III.23 on the everywhere valid nonexplosive arrival domain.
-/

@[expose] public section

open MeasureTheory
open scoped NNReal ENNReal

namespace ProbabilityTheory.IsNonexplosiveArrivalSequence

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
  {Γ : ℕ → Ω → WithTop ℝ≥0}

/-- The original count has the actual compensation domain in the genuine
usual natural augmentation, without any expected-count assumption. -/
theorem count_compensator_domain_natural_usual
    (hΓ : ∀ ω, IsNonexplosiveArrivalSequence (fun k ↦ Γ k ω))
    (hMeas : ∀ k, Measurable (Γ k)) :
    let F := Filtration.natural (fun s ω ↦ (hΓ ω).count s)
      (fun s ↦ (measurable_count hΓ hMeas s).stronglyMeasurable)
    let C := fun (t : ℝ≥0) (ω : NullMeasurableSpace Ω P) ↦ ((hΓ ω).count t : ℝ)
    Adapted (F.usualAugmentation P) C ∧ HasCadlagPaths C P.completion ∧
      HasLocallyIntegrableVariation C (F.usualAugmentation P) P.completion := by
  let F := Filtration.natural (fun s ω ↦ (hΓ ω).count s)
    (fun s ↦ (measurable_count hΓ hMeas s).stronglyMeasurable)
  let G := F.usualAugmentation P
  let N := fun (t : ℝ≥0) (ω : NullMeasurableSpace Ω P) ↦ (hΓ ω).count t
  have haRaw : Adapted F (fun t ω ↦ (hΓ ω).count t) :=
    (Filtration.stronglyAdapted_natural
      (fun s ↦ (measurable_count hΓ hMeas s).stronglyMeasurable)).adapted
  have ha : Adapted G N := fun t ↦ (haRaw t).mono (F.le_usualAugmentation P t) le_rfl
  have hmΓ (n : ℕ) : Measurable (fun ω : NullMeasurableSpace Ω P ↦ Γ n ω) :=
    fun B hB ↦ (hMeas n hB).nullMeasurableSet (μ := P)
  have hN : IsNonexplosiveCountingProcess N P.completion :=
    isNonexplosiveCountingProcess_count
      (fun ω : NullMeasurableSpace Ω P ↦ hΓ ω) hmΓ P.completion
  exact ⟨ha.natCast_real, hN.hasCadlagPaths_real,
    hN.hasLocallyIntegrableVariation_real ha (F.usualAugmentation_isUsual P)⟩

/-- The existing canonical compensator is indistinguishable from the
original conditional-gap hazard series, with all kernels computed under
the original probability measure and all histories taken before their
indexed arrival. No compensator or local-martingale certificate is an input. -/
theorem predictableCompensator_count_eq_conditional_hazard_sum
    (hΓ : ∀ ω, IsNonexplosiveArrivalSequence (fun k ↦ Γ k ω))
    (hMeas : ∀ k, Measurable (Γ k)) :
    let : StandardBorelSpace (WithTop ℝ≥0) := inferInstanceAs (StandardBorelSpace ℝ≥0∞)
    let F := Filtration.natural (fun s ω ↦ (hΓ ω).count s)
      (fun s ↦ (measurable_count hΓ hMeas s).stronglyMeasurable)
    let H := fun (n : ℕ) (ω : Ω) (i : Fin n) ↦ Γ i ω
    let L := fun n ↦
      Nat.casesOn (motive := fun _ ↦ Ω → WithTop ℝ≥0) n (fun _ ↦ 0) Γ
    let S := fun (n : ℕ) (ω : Ω) ↦ arrivalInterarrival (fun k ↦ Γ k ω) n
    let κ := fun n ↦ condDistrib (S n) (H n) P
    let D := fun n ↦ stoppedProcess
      (fun (s : ℝ≥0) (ω : Ω) ↦ if L n ω ≤ (s : WithTop ℝ≥0)
        then (eCumulativeHazard (κ n (H n ω)) (s - (L n ω).untopA)).toReal else 0) (Γ n)
    let hC := count_compensator_domain_natural_usual (P := P) hΓ hMeas
    Indistinguishable
      (hC.2.2.predictableCompensator hC.1 (F.usualAugmentation_isUsual P) hC.2.1)
      (fun (t : ℝ≥0) (ω : NullMeasurableSpace Ω P) ↦ ∑' n, D n t ω)
      P.completion := by
  classical
  let : StandardBorelSpace (WithTop ℝ≥0) := inferInstanceAs (StandardBorelSpace ℝ≥0∞)
  let F := Filtration.natural (fun s ω ↦ (hΓ ω).count s)
    (fun s ↦ (measurable_count hΓ hMeas s).stronglyMeasurable)
  let G := F.usualAugmentation P
  let H := fun (n : ℕ) (ω : Ω) (i : Fin n) ↦ Γ i ω
  let L := fun n ↦
    Nat.casesOn (motive := fun _ ↦ Ω → WithTop ℝ≥0) n (fun _ ↦ 0) Γ
  let S := fun (n : ℕ) (ω : Ω) ↦ arrivalInterarrival (fun k ↦ Γ k ω) n
  let κ := fun n ↦ condDistrib (S n) (H n) P
  let D := fun n ↦ stoppedProcess
    (fun (s : ℝ≥0) (ω : Ω) ↦ if L n ω ≤ (s : WithTop ℝ≥0)
      then (eCumulativeHazard (κ n (H n ω)) (s - (L n ω).untopA)).toReal else 0) (Γ n)
  let A := fun (t : ℝ≥0) (ω : NullMeasurableSpace Ω P) ↦ ∑' n, D n t ω
  let C := fun (t : ℝ≥0) (ω : NullMeasurableSpace Ω P) ↦ ((hΓ ω).count t : ℝ)
  have hC := count_compensator_domain_natural_usual (P := P) hΓ hMeas
  have hsum := predictable_zero_paths_conditional_hazard_sum (P := P) hΓ hMeas
  have hpred : F.predictable ≤ G.predictable := by
    apply measurableSpace_le_predictable_of_measurableSet
    · intro E hE
      exact measurableSet_predictable_singleton_bot_prod (F.le_usualAugmentation P 0 E hE)
    · intro t E hE
      exact measurableSet_predictable_Ioi_prod (F.le_usualAugmentation P t E hE)
  have hpA : IsStronglyPredictable G A := hsum.1.mono hpred
  have hmA : HasMonotonePaths A P.completion := hsum.2.2.1.mono fun _ hω ↦ hω.1
  have hA0 : A 0 =ᵐ[P.completion] 0 := ae_of_all _ fun ω ↦ congrFun hsum.2.1 ω
  have hM : IsLocalMartingale (C - A) G P.completion :=
    isLocalMartingale_count_sub_conditional_hazard_sum hΓ hMeas
  exact hC.2.2.predictableCompensator_unique hC.1 (F.usualAugmentation_isUsual P)
    hC.2.1 hpA hmA.hasFiniteVariationPaths hA0 hM

end ProbabilityTheory.IsNonexplosiveArrivalSequence
