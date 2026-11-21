/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.Counting.ArrivalConstruction
public import StochLean.Probability.Process.Filtration.Usual
public import StochLean.Probability.Process.Stopping.Restriction

/-! # Counts from almost-everywhere valid arrival data

Initial completeness makes the common null set of invalid arrival paths
measurable at time zero. Restriction by its complement uses the existing
`restrictedStoppingTime`: each invalid path becomes the valid sequence
constantly equal to infinity, while valid paths remain unchanged.

Only the resulting everywhere-valid representative is passed to the
guarded count. On one common almost-sure event this count is exactly the
original valid path's guarded count at every time, and its actual native
arrival clocks recover the original coordinates. No count is assigned to
an invalid raw arrival sequence by an unproved fallback convention.

Only initial completeness is used. Right continuity of the filtration,
predictability of the arrivals and finiteness of the measure are not needed.
-/

@[expose] public section

open MeasureTheory Filter Set
open scoped NNReal Topology

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
  {F : Filtration ℝ≥0 mΩ} {Γ : ℕ → Ω → WithTop ℝ≥0}

/-- Initial completeness permits a common stopping-time representative
whose arrival paths are valid everywhere. The witness restricts every
original clock to the same good event and is infinite off that event. -/
theorem exists_nonexplosiveArrivalSequence_version
    (hc0 : IsCompleteSubMeasurableSpace P (F 0))
    (hstop : ∀ n, IsStoppingTime F (Γ n))
    (hvalid : ∀ᵐ ω ∂P, IsNonexplosiveArrivalSequence (fun n ↦ Γ n ω)) :
    ∃ Γ' : ℕ → Ω → WithTop ℝ≥0,
      (∀ ω, IsNonexplosiveArrivalSequence (fun n ↦ Γ' n ω)) ∧
      (∀ n, IsStoppingTime F (Γ' n)) ∧ (∀ᵐ ω ∂P, ∀ n, Γ' n ω = Γ n ω) := by
  classical
  let bad := {ω | ¬ IsNonexplosiveArrivalSequence (fun n ↦ Γ n ω)}
  have hgood : MeasurableSet[F 0] badᶜ := (hc0 bad (ae_iff.mp hvalid)).compl
  let Γ' (n : ℕ) := restrictedStoppingTime (Γ n) badᶜ
  have hΓ' : ∀ ω, IsNonexplosiveArrivalSequence (fun n ↦ Γ' n ω) := by
    intro ω
    by_cases hω : ω ∈ badᶜ
    · have he : (fun n ↦ Γ' n ω) = fun n ↦ Γ n ω :=
        funext fun n ↦ restrictedStoppingTime_of_mem (Γ n) hω
      rw [he]
      change ¬ ¬ IsNonexplosiveArrivalSequence (fun n ↦ Γ n ω) at hω
      exact not_not.mp hω
    · have he : (fun n ↦ Γ' n ω) = fun _ ↦ ⊤ :=
        funext fun n ↦ restrictedStoppingTime_of_notMem (Γ n) hω
      rw [he]
      exact ⟨fun _ ↦ bot_lt_top, fun _ _ _ ↦ le_rfl,
        fun _ hfin ↦ False.elim (hfin rfl), tendsto_const_nhds⟩
  have hs' (n : ℕ) : IsStoppingTime F (Γ' n) := by
    have hle : F 0 ≤ (hstop n).measurableSpace :=
      (hstop n).le_measurableSpace_of_const_le fun _ ↦ bot_le
    exact (hstop n).restrictedStoppingTime (hle _ hgood)
  refine ⟨Γ', hΓ', hs', ?_⟩
  filter_upwards [hvalid] with ω hω n
  exact restrictedStoppingTime_of_mem (Γ n) (show ω ∈ badᶜ from fun hb ↦ hb hω)

/-- Almost-everywhere valid stopping-time arrivals construct an adapted
nonexplosive count through an everywhere-valid representative. The final
clause explicitly identifies the count on each good original path using
that path's actual nonexplosion proof, simultaneously at every time. -/
theorem exists_countingProcess_of_ae_nonexplosive_arrivals
    (hc0 : IsCompleteSubMeasurableSpace P (F 0))
    (hstop : ∀ n, IsStoppingTime F (Γ n))
    (hvalid : ∀ᵐ ω ∂P, IsNonexplosiveArrivalSequence (fun n ↦ Γ n ω)) :
    ∃ Γ' : ℕ → Ω → WithTop ℝ≥0,
      ∃ hΓ' : ∀ ω, IsNonexplosiveArrivalSequence (fun n ↦ Γ' n ω),
        let N := fun t ω ↦ (hΓ' ω).count t
        IsNonexplosiveCountingProcess N P ∧ Adapted F N ∧
          (∀ᵐ ω ∂P, ∀ n, hittingAfter N (Ioi n) 0 ω = Γ n ω) ∧
          (∀ᵐ ω ∂P, ∃ hω : IsNonexplosiveArrivalSequence (fun n ↦ Γ n ω),
            ∀ t : ℝ≥0, N t ω = hω.count t) := by
  obtain ⟨Γ', hΓ', hs', he⟩ :=
    exists_nonexplosiveArrivalSequence_version hc0 hstop hvalid
  refine ⟨Γ', hΓ', ?_⟩
  dsimp only
  refine ⟨IsNonexplosiveArrivalSequence.isNonexplosiveCountingProcess_count hΓ'
    (fun n ↦ (hs' n).measurable') P,
    (IsNonexplosiveArrivalSequence.adapted_count_iff hΓ' F).mpr hs', ?_, ?_⟩
  · filter_upwards [he] with ω hω n
    exact (congrFun (IsNonexplosiveArrivalSequence.hittingAfter_count_eq hΓ' n) ω).trans
      (hω n)
  · filter_upwards [hvalid, he] with ω hω heω
    refine ⟨hω, ?_⟩
    intro t
    apply Nat.le_antisymm
    · apply ((hΓ' ω).count_le_iff t (hω.count t)).mpr
      rw [heω (hω.count t)]
      exact hω.lt_arrival_count t
    · apply (hω.count_le_iff t ((hΓ' ω).count t)).mpr
      rw [← heω ((hΓ' ω).count t)]
      exact (hΓ' ω).lt_arrival_count t

end ProbabilityTheory
