/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.Counting.ArrivalHazardMartingale
public import StochLean.Probability.Process.Counting.ArrivalHazardSum
public import StochLean.Probability.Process.Counting.ArrivalLocalizing
public import StochLean.Probability.Process.Counting.ArrivalRightContinuous
public import StochLean.Probability.Process.Counting.ArrivalStoppedSum
public import StochLean.Probability.Process.Filtration.MartingaleAugmentation
public import StochLean.Probability.Process.LocalMartingale.Reducing
public import StochLean.Probability.Process.Path.RightStep
public import StochLean.Probability.Process.Path.Subtraction

/-! # Localization of the actual conditional arrival-hazard sum

The original count minus its genuine conditional-hazard series is a local
martingale in the genuine usual augmentation of the count's raw natural
filtration. Every conditional distribution is computed from the original
measure, before completion; no conditional law is silently recomputed.

Finite prefixes are true UI martingales by the actual stage theorem. Raw
right continuity transfers them to the completed usual filtration, where
ordinary stopping at an original arrival preserves UI. The exact stopped
prefix identity identifies these stopped finite martingales with the stopped
total process. In particular the next stage vanishes at its birth endpoint;
it is not discarded merely by an insufficient count inequality.

The original positive, monotone, diverging arrival sequence supplies a
genuine unmasked reducing sequence and hence the existing canonical masked
local-martingale predicate. The total series's adaptedness and common-event
cadlag paths are independently obtained from the actual sum theorem.
No finite expected total count, global series moment, supplied compensator
or local-martingale certificate is assumed.
-/

@[expose] public section

open MeasureTheory Filter Set
open scoped NNReal ENNReal

namespace ProbabilityTheory

private theorem standardBorel_arrivalHazardLocalization :
    StandardBorelSpace (WithTop ℝ≥0) :=
  inferInstanceAs (StandardBorelSpace ℝ≥0∞)

attribute [local instance] standardBorel_arrivalHazardLocalization

namespace IsNonexplosiveArrivalSequence

/-- The actual count minus its conditional-hazard series is a local
martingale in the genuine usual natural-count augmentation. -/
theorem isLocalMartingale_count_sub_conditional_hazard_sum
    {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
    {Γ : ℕ → Ω → WithTop ℝ≥0}
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
    IsLocalMartingale
      (fun (t : ℝ≥0) (ω : NullMeasurableSpace Ω P) ↦
        ((hΓ ω).count t : ℝ) - ∑' n : ℕ, D n t ω)
      (F.usualAugmentation P) P.completion := by
  classical
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
  let A : ℝ≥0 → Ω → ℝ := fun t ω ↦ ∑' n : ℕ, D n t ω
  let C : ℝ≥0 → Ω → ℝ := fun t ω ↦ ((hΓ ω).count t : ℝ)
  let M : ℕ → ℝ≥0 → Ω → ℝ := fun n t ω ↦
    (if Γ n ω ≤ (t : WithTop ℝ≥0) then 1 else 0) - D n t ω
  let Q : ℕ → ℝ≥0 → Ω → ℝ := fun k t ω ↦ ∑ n ∈ Finset.range k, M n t ω
  let F' := F.usualAugmentation P
  let W : ℝ≥0 → NullMeasurableSpace Ω P → ℝ := fun t ω ↦ C t ω - A t ω
  change IsLocalMartingale W F' P.completion
  have hF : F.IsRightContinuous := natural_count_isRightContinuous hΓ hMeas
  have hF' : F'.IsUsual P.completion := F.usualAugmentation_isUsual P
  have hstage (n : ℕ) : IsUIMartingale (M n) F P :=
    martingale_uniformIntegrable_arrival_sub_conditional_hazard hΓ hMeas n
  have hDpath (n : ℕ) : ∀ᵐ ω ∂P,
      Monotone (fun t ↦ D n t ω) ∧ IsCadlagPath (fun t ↦ D n t ω) :=
    (predictable_zero_monotone_cadlag_delayed_hazard (P := P) hΓ hMeas n).2.2
  have hcM (n : ℕ) : HasCadlagPaths (M n) P := by
    filter_upwards [hDpath n] with ω hω
    have hc : IsCadlagPath (fun t : ℝ≥0 ↦
        if Γ n ω ≤ (t : WithTop ℝ≥0) then (1 : ℝ) else 0) := by
      simpa only [indicator_apply, mem_ofPred_eq] using
        isCadlagPath_indicator_lifetime_le (Γ n) (fun _ ↦ (1 : ℝ)) ω
    exact hc.sub hω.2
  have hQ (k : ℕ) : IsUIMartingale (Q k) F P ∧ HasCadlagPaths (Q k) P := by
    induction k with
    | zero =>
        have hu0 : UniformIntegrable (fun (_ : ℝ≥0) (_ : Ω) ↦ (0 : ℝ)) 1 P :=
          uniformIntegrable_const le_rfl (by simp) (memLp_const 0)
        have hc0 : HasCadlagPaths (fun (_ : ℝ≥0) (_ : Ω) ↦ (0 : ℝ)) P :=
          ae_of_all P fun _ ↦ IsContinuousPath.isCadlagPath continuous_const
        simpa only [Q, Finset.range_zero, Finset.sum_empty] using
          (show IsUIMartingale (fun (_ : ℝ≥0) (_ : Ω) ↦ (0 : ℝ)) F P ∧
            HasCadlagPaths (fun (_ : ℝ≥0) (_ : Ω) ↦ (0 : ℝ)) P from
              ⟨⟨martingale_const F P 0, hu0⟩, hc0⟩)
    | succ k ih =>
        have he : Q (k + 1) = Q k + M k := by
          funext t ω
          simp only [Q, Finset.sum_range_succ, Pi.add_apply]
        rw [he]
        exact ⟨ih.1.add (hstage k), ih.2.add (hcM k)⟩
  have hsum := predictable_zero_paths_conditional_hazard_sum (P := P) hΓ hMeas
  have haN : Adapted F (fun t ω ↦ (hΓ ω).count t) :=
    (Filtration.stronglyAdapted_natural
      (fun s ↦ (measurable_count hΓ hMeas s).stronglyMeasurable)).adapted
  have haC : Adapted F C := haN.natCast_real
  have haA : Adapted F A := hsum.1.stronglyAdapted.adapted
  have haW : Adapted F' W := fun t ↦
    ((haC t).sub (haA t)).mono (F.le_usualAugmentation P t) le_rfl
  have hcC : HasCadlagPaths C P :=
    (isNonexplosiveCountingProcess_count hΓ hMeas P).hasCadlagPaths_real
  have hcA : HasCadlagPaths A P := hsum.2.2.1.mono fun _ hω ↦ hω.2
  have hcW : HasCadlagPaths W P.completion := hcC.sub hcA
  have hΓraw : IsLocalizingSequence F Γ P :=
    (isLocalizingSequence_natural_count hΓ hMeas P).1
  have hΓ' : IsPreLocalizingSequence F' Γ P.completion :=
    ⟨fun n t ↦ F.le_usualAugmentation P t _ (hΓraw.isStoppingTime n t),
      hΓraw.tendsto_top⟩
  have hzero : ∀ n : ℕ,
      let L' : Ω → WithTop ℝ≥0 :=
        Nat.casesOn (motive := fun _ ↦ Ω → WithTop ℝ≥0) n (fun _ ↦ 0) Γ
      ∀ (t : ℝ≥0) ω, (t : WithTop ℝ≥0) ≤ L' ω → D n t ω = 0 := by
    intro n
    change ∀ (t : ℝ≥0) ω, (t : WithTop ℝ≥0) ≤ L n ω → D n t ω = 0
    intro t ω ht
    exact stoppedProcess_delayed_eCumulativeHazard_eq_zero_of_le (κ n) (H n) ht
  have hK : IsKlenkeLocalizingSequence W F' P.completion Γ := by
    refine ⟨hΓ', fun i j hij ω ↦ (hΓ ω).monotone hij, fun m ↦ ?_⟩
    have he : stoppedProcess W (Γ m) =
        stoppedProcess (fun t (ω : NullMeasurableSpace Ω P) ↦ Q (m + 1) t ω) (Γ m) :=
      stoppedProcess_count_sub_tsum_eq_sum_range hΓ D hzero m
    rw [he]
    have hu : IsUIMartingale
        (fun t (ω : NullMeasurableSpace Ω P) ↦ Q (m + 1) t ω) F' P.completion :=
      (hQ (m + 1)).1.usualAugmentation_of_isRightContinuous hF
    have hc : HasCadlagPaths
        (fun t (ω : NullMeasurableSpace Ω P) ↦ Q (m + 1) t ω) P.completion :=
      (hQ (m + 1)).2
    exact hu.stoppedProcess_of_usual hF' hc.hasRightContinuousPaths (hΓ'.isStoppingTime m)
  exact hK.isLocalMartingale haW hcW

end IsNonexplosiveArrivalSequence
end ProbabilityTheory
