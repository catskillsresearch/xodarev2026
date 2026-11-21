/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.Counting.ArrivalHazardPaths
public import StochLean.Probability.Process.Path.LocallyFiniteSeries
public import Mathlib.MeasureTheory.Constructions.Polish.StronglyMeasurable

/-! # The actual locally finite sum of conditional arrival hazards

At a finite horizon the original count bounds the active hazard indices.
The current, still pending stage is included: the finite prefix ends at
index `count t`, not at `count t - 1`. All higher stages are identically zero
throughout that horizon. Thus the original series is genuinely summable,
and no integrable total count or globally summable series bound is needed.

Native measurability of a real series gives exact predictability. Countably
many stage path events give a single full-measure event supporting monotone
cadlag paths for the total series, by its actual compact finite support.
This formula is not a second compensator selector. Identification with the
existing canonical compensator additionally needs the local martingale proof.
-/

@[expose] public section

open MeasureTheory Filter
open scoped NNReal ENNReal

namespace ProbabilityTheory.IsNonexplosiveArrivalSequence

/-- The genuine sum of actual conditional hazards is predictable, starts
at zero, and has monotone cadlag paths on one common event. Its pointwise
finite-prefix formula retains the current pending stage. -/
theorem predictable_zero_paths_conditional_hazard_sum
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
    let A := fun (t : ℝ≥0) (ω : Ω) ↦ ∑' n, D n t ω
    IsStronglyPredictable F A ∧ A 0 = 0 ∧
      (∀ᵐ ω ∂P, Monotone (fun t ↦ A t ω) ∧ IsCadlagPath (fun t ↦ A t ω)) ∧
      ∀ t ω, Summable (fun n ↦ D n t ω) ∧
        A t ω = ∑ n ∈ Finset.range ((hΓ ω).count t + 1), D n t ω := by
  classical
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
  let A := fun (t : ℝ≥0) (ω : Ω) ↦ ∑' n, D n t ω
  change IsStronglyPredictable F A ∧ A 0 = 0 ∧
    (∀ᵐ ω ∂P, Monotone (fun t ↦ A t ω) ∧ IsCadlagPath (fun t ↦ A t ω)) ∧
    ∀ t ω, Summable (fun n ↦ D n t ω) ∧
      A t ω = ∑ n ∈ Finset.range ((hΓ ω).count t + 1), D n t ω
  have hd (n : ℕ) : IsStronglyPredictable F (D n) ∧ D n 0 = 0 ∧
      ∀ᵐ ω ∂P, Monotone (fun t ↦ D n t ω) ∧ IsCadlagPath (fun t ↦ D n t ω) :=
    predictable_zero_monotone_cadlag_delayed_hazard hΓ hMeas n
  have hz (ω : Ω) (T : ℝ≥0) (n : ℕ) (hn : (hΓ ω).count T + 1 ≤ n)
      (t : ℝ≥0) (ht : t ≤ T) : D n t ω = 0 :=
    stoppedProcess_delayed_eCumulativeHazard_eq_zero_of_count_lt
      (κ n) (H n) hΓ n ht ω (Nat.lt_of_succ_le hn)
  have hloc (ω : Ω) : ∀ T : ℝ≥0, ∃ N : ℕ,
      ∀ n, N ≤ n → ∀ t, t ≤ T → D n t ω = 0 :=
    fun T ↦ ⟨(hΓ ω).count T + 1, hz ω T⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · let : MeasurableSpace (ℝ≥0 × Ω) := F.predictable
    change StronglyMeasurable (fun p : ℝ≥0 × Ω ↦ ∑' n, D n p.1 p.2)
    exact StronglyMeasurable.tsum (L := SummationFilter.unconditional ℕ) (fun n ↦ (hd n).1)
  · funext ω
    change (∑' n, D n 0 ω) = 0
    have h0 (n : ℕ) : D n 0 ω = 0 := congrFun (hd n).2.1 ω
    simp only [h0, tsum_zero]
  · filter_upwards [ae_all_iff.mpr (fun n ↦ (hd n).2.2)] with ω hω
    exact monotone_isCadlagPath_tsum_of_locally_finite (hloc ω)
      (fun n ↦ (hω n).1) (fun n ↦ (hω n).2)
  · intro t ω
    refine ⟨(summable_tendstoUniformlyOn_tsum_of_locally_finite (hloc ω)).1 t, ?_⟩
    apply tsum_eq_sum
    intro n hn
    exact hz ω t n (Nat.le_of_not_gt (fun h ↦ hn (Finset.mem_range.mpr h))) t le_rfl

end ProbabilityTheory.IsNonexplosiveArrivalSequence
