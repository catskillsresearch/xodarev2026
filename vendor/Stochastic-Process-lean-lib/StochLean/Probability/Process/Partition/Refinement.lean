/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.Partition
public import Mathlib.Data.Fin.Tuple.Basic

/-! # Common refinements of finite stopping-time partitions

Refinement is pathwise endpoint inclusion, so random coincidences and repeated endpoints
are allowed. Splitting at one finite stopping time uses only minima and maxima of stopping
times. The witness construction is deliberately nonminimal; it requires no measurable sorting
choice and does not impose boundedness or additional conditions on the filtration.
-/

@[expose] public section

open MeasureTheory Set
open scoped NNReal

namespace ProbabilityTheory.StoppingTimePartition

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {F : Filtration ℝ≥0 mΩ}

/-- Every old endpoint occurs in the new partition at every sample. -/
def Refines (ρ π : StoppingTimePartition F) : Prop :=
  ∀ ω i, ∃ j, ρ.point j ω = π.point i ω

theorem Refines.refl (π : StoppingTimePartition F) : π.Refines π :=
  fun _ i ↦ ⟨i, rfl⟩

theorem Refines.trans {ρ π κ : StoppingTimePartition F}
    (hρπ : ρ.Refines π) (hπκ : π.Refines κ) : ρ.Refines κ := by
  intro ω i
  obtain ⟨j, hj⟩ := hπκ ω i
  obtain ⟨k, hk⟩ := hρπ ω j
  exact ⟨k, hk.trans hj⟩

/-- The first block is capped at `τ`; the second block is raised to `τ`.
The possible gap between the blocks will carry a zero coefficient. -/
def splitAt (π : StoppingTimePartition F) (τ : FiniteStoppingTime F) :
    StoppingTimePartition F where
  size := π.size + 1 + π.size
  point := Fin.append (m := π.size + 1) (n := π.size + 1)
    (fun i ↦ (π.point i).min τ) (fun i ↦ (π.point i).max τ)
  monotone_point := by
    intro ω
    refine Fin.addCases (m := π.size + 1) (n := π.size + 1) (fun i ↦ ?_) (fun i ↦ ?_)
    · refine Fin.addCases (m := π.size + 1) (n := π.size + 1)
        (fun j hij ↦ ?_) (fun j _ ↦ ?_)
      · simp only [Fin.append_left, FiniteStoppingTime.min_apply]
        exact min_le_min_right _ (π.monotone_point ω (by exact hij))
      · simp only [Fin.append_left, Fin.append_right, FiniteStoppingTime.min_apply,
          FiniteStoppingTime.max_apply]
        exact (min_le_right _ _).trans (le_max_right _ _)
    · refine Fin.addCases (m := π.size + 1) (n := π.size + 1)
        (fun j hij ↦ ?_) (fun j hij ↦ ?_)
      · have hi := i.isLt
        have hj := j.isLt
        simp only [Fin.le_def, Fin.val_natAdd, Fin.val_castAdd] at hij
        omega
      · simp only [Fin.append_right, FiniteStoppingTime.max_apply]
        exact max_le_max_right _ (π.monotone_point ω (by simpa using hij))
  first_eq_zero := by
    intro ω
    change Fin.append (α := FiniteStoppingTime F) _ _
      ((0 : Fin (π.size + 1)).castAdd (π.size + 1)) ω = 0
    simp only [Fin.append_left, FiniteStoppingTime.min_apply, π.first_eq_zero]
    exact min_eq_left bot_le

theorem splitAt_refines (π : StoppingTimePartition F) (τ : FiniteStoppingTime F) :
    (π.splitAt τ).Refines π := by
  intro ω i
  by_cases hi : π.point i ω ≤ τ ω
  · refine ⟨i.castAdd (π.size + 1), ?_⟩
    change Fin.append (α := FiniteStoppingTime F) _ _ (i.castAdd (π.size + 1)) ω = _
    simp only [Fin.append_left, FiniteStoppingTime.min_apply, min_eq_left hi]
  · refine ⟨i.natAdd (π.size + 1), ?_⟩
    change Fin.append (α := FiniteStoppingTime F) _ _ (i.natAdd (π.size + 1)) ω = _
    simp only [Fin.append_right, FiniteStoppingTime.max_apply, max_eq_left (le_of_not_ge hi)]

theorem splitAt_contains (π : StoppingTimePartition F) (τ : FiniteStoppingTime F) (ω : Ω) :
    ∃ j, (π.splitAt τ).point j ω = τ ω := by
  refine ⟨(0 : Fin (π.size + 1)).natAdd (π.size + 1), ?_⟩
  change Fin.append (α := FiniteStoppingTime F) _ _
    ((0 : Fin (π.size + 1)).natAdd (π.size + 1)) ω = _
  simp only [Fin.append_right, FiniteStoppingTime.max_apply, π.first_eq_zero]
  exact max_eq_right bot_le

theorem exists_refinement_containing (π : StoppingTimePartition F)
    (s : Finset (FiniteStoppingTime F)) :
    ∃ ρ : StoppingTimePartition F, ρ.Refines π ∧
      ∀ τ ∈ s, ∀ ω, ∃ j, ρ.point j ω = τ ω := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨π, .refl π, by simp⟩
  | @insert τ s _ ih =>
    obtain ⟨ρ, hρ, hs⟩ := ih
    refine ⟨ρ.splitAt τ, (ρ.splitAt_refines τ).trans hρ, ?_⟩
    intro σ hσ ω
    rcases Finset.mem_insert.mp hσ with hστ | hσ
    · subst σ
      exact ρ.splitAt_contains τ ω
    · obtain ⟨i, hi⟩ := hs σ hσ ω
      obtain ⟨j, hj⟩ := ρ.splitAt_refines τ ω i
      exact ⟨j, hj.trans hi⟩

/-- Two arbitrary source partitions admit one common finite stopping-time refinement. -/
theorem exists_common_refinement (π κ : StoppingTimePartition F) :
    ∃ ρ : StoppingTimePartition F, ρ.Refines π ∧ ρ.Refines κ := by
  classical
  obtain ⟨ρ, hρ, hs⟩ := π.exists_refinement_containing (Finset.univ.image κ.point)
  exact ⟨ρ, hρ, fun ω i ↦ hs _ (Finset.mem_image_of_mem _ (Finset.mem_univ i)) ω⟩

theorem Refines.terminal_le {ρ π : StoppingTimePartition F} (h : ρ.Refines π) (ω : Ω) :
    π.terminal ω ≤ ρ.terminal ω := by
  obtain ⟨j, hj⟩ := h ω (Fin.last π.size)
  exact hj ▸ ρ.monotone_point ω (Fin.le_last j)

/-- An old boundary cannot lie strictly inside a cell of the refinement. -/
theorem Refines.point_lt_iff_le_left {ρ π : StoppingTimePartition F} (h : ρ.Refines π)
    {ω : Ω} {t : ℝ≥0} {i : Fin ρ.size}
    (ht : ρ.point i.castSucc ω < t ∧ t ≤ ρ.point i.succ ω) (k : Fin (π.size + 1)) :
    π.point k ω < t ↔ π.point k ω ≤ ρ.point i.castSucc ω := by
  constructor
  · intro hk
    obtain ⟨j, hj⟩ := h ω k
    rw [← hj] at hk ⊢
    by_cases hji : j ≤ i.castSucc
    · exact ρ.monotone_point ω hji
    · have hij : i.succ ≤ j := by
        simp only [Fin.le_def, Fin.val_castSucc, Fin.val_succ] at hji ⊢
        omega
      exact False.elim (not_lt_of_ge (ht.2.trans (ρ.monotone_point ω hij)) hk)
  · exact fun hk ↦ hk.trans_lt ht.1

theorem Refines.le_point_iff_left_lt {ρ π : StoppingTimePartition F} (h : ρ.Refines π)
    {ω : Ω} {t : ℝ≥0} {i : Fin ρ.size}
    (ht : ρ.point i.castSucc ω < t ∧ t ≤ ρ.point i.succ ω) (k : Fin (π.size + 1)) :
    t ≤ π.point k ω ↔ ρ.point i.castSucc ω < π.point k ω := by
  simpa only [not_lt, not_le] using not_congr (h.point_lt_iff_le_left ht k)

end ProbabilityTheory.StoppingTimePartition
