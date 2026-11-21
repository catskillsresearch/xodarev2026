/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.Counting.ArrivalConstruction

/-! # Arrival histories at the previous arrival time

In the raw natural filtration of the actual nonexplosive count, every
original arrival is a stopping time. At the start of stage `n`, the first
`n` arrivals are measurable in the native stopping-time sigma field. The
start of stage zero is the constant zero time and its history is empty;
the start of stage `n + 1` is the original arrival of index `n`.

Only arrivals no later than the stage's starting time are used. Infinite
arrival times remain extended times, with no finiteness or probability
assumption and no new history or stopping-time selector.
-/

@[expose] public section

open MeasureTheory
open scoped NNReal

namespace ProbabilityTheory.IsNonexplosiveArrivalSequence

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {Γ : ℕ → Ω → WithTop ℝ≥0}

/-- All original arrivals are stopping times in the actual count's raw
natural filtration, and the first `n` arrivals are measurable at the
previous arrival, with the empty history observed at time zero. -/
theorem isStoppingTime_and_measurable_history_natural_count
    (hΓ : ∀ ω, IsNonexplosiveArrivalSequence (fun k ↦ Γ k ω))
    (hMeas : ∀ k, Measurable (Γ k)) :
    let F := Filtration.natural (fun s ω ↦ (hΓ ω).count s)
      (fun s ↦ (measurable_count hΓ hMeas s).stronglyMeasurable)
    (∀ k, IsStoppingTime F (Γ k)) ∧ ∀ n : ℕ,
      let L : Ω → WithTop ℝ≥0 := n.casesOn (fun _ ↦ 0) Γ
      ∃ hL : IsStoppingTime F L,
        @Measurable Ω (Fin n → WithTop ℝ≥0)
          (IsStoppingTime.measurableSpace (m := mΩ) (f := F) (τ := L) hL)
          inferInstance (fun ω (i : Fin n) ↦ Γ i ω) := by
  intro F
  have ha : StronglyAdapted F (fun s ω ↦ (hΓ ω).count s) :=
    Filtration.stronglyAdapted_natural
      (fun s ↦ (measurable_count hΓ hMeas s).stronglyMeasurable)
  have hstop : ∀ k, IsStoppingTime F (Γ k) := (adapted_count_iff hΓ F).mp ha.adapted
  refine ⟨hstop, ?_⟩
  intro n
  cases n with
  | zero =>
      let hL : IsStoppingTime F (fun _ ↦ (0 : WithTop ℝ≥0)) :=
        isStoppingTime_const F (0 : ℝ≥0)
      refine ⟨hL, ?_⟩
      exact @measurable_pi_lambda _ _ _ hL.measurableSpace _ _ fun i ↦ Fin.elim0 i
  | succ k =>
      refine ⟨hstop k, ?_⟩
      refine @measurable_pi_lambda _ _ _ (hstop k).measurableSpace _ _ fun i ↦ ?_
      exact (hstop i).measurable.mono
        ((hstop i).measurableSpace_mono (hstop k)
          (fun ω ↦ (hΓ ω).monotone (Nat.lt_succ_iff.mp i.isLt))) le_rfl

end ProbabilityTheory.IsNonexplosiveArrivalSequence
