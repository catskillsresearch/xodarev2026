/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.Stopping.PredictableComparison
public import StochLean.Probability.Process.Stopping.PredictableRestriction

/-! # Disjoint finite graphs for a sequence of predictable times

Restrict each predictable time to the event that no earlier index represents
the same finite lifetime. The comparison events are measurable strictly before
that time, so the existing predictable-restriction theorem applies. The least
index realizing a finite graph point preserves it exactly, including time zero.
The restricted finite graphs are pairwise disjoint on every path.

A positive-time version further restricts to the positive-lifetime event.
Its times are strictly positive everywhere (infinity is allowed), and their
graphs cover precisely the positive part of the original graph union. This
separates positive jumps from the source initial-jump convention.

All graph statements use the existing finite `stoppingTimeGraph` owner.
No graph point or process value at infinity is introduced.
-/

@[expose] public section

open MeasureTheory Set
open scoped NNReal

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsFiniteMeasure P]
  {F : Filtration ℝ≥0 mΩ}

/-- Actual predictable restrictions make the finite graphs pairwise disjoint,
while preserving their union exactly, including its zero-time section. -/
theorem exists_predictableStoppingTime_disjoint_graph_restrictions
    (σ : ℕ → Ω → WithTop ℝ≥0) (hσ : ∀ n, IsPredictableStoppingTime F (σ n) P)
    (hF : F.IsUsual P) :
    ∃ ρ : ℕ → Ω → WithTop ℝ≥0,
      (∀ n, IsPredictableStoppingTime F (ρ n) P) ∧
        (∀ n, stoppingTimeGraph (ρ n) ⊆ stoppingTimeGraph (σ n)) ∧
          Pairwise (fun n m ↦ Disjoint (stoppingTimeGraph (ρ n)) (stoppingTimeGraph (ρ m))) ∧
            (⋃ n, stoppingTimeGraph (ρ n)) = ⋃ n, stoppingTimeGraph (σ n) := by
  classical
  let E (n : ℕ) : Set Ω := {ω | ∀ k < n, ¬ (σ k ω = σ n ω ∧ σ n ω ≠ ⊤)}
  have hE (n : ℕ) : MeasurableSet[(hσ n).1.measurableSpaceBefore] (E n) := by
    have he : E n = ⋂ k : ℕ, ⋂ _ : k < n, {ω | σ k ω = σ n ω ∧ σ n ω ≠ ⊤}ᶜ := by
      ext ω
      simp only [E, mem_ofPred_eq, mem_iInter, mem_compl_iff]
    rw [he]
    exact MeasurableSet.iInter fun k ↦ MeasurableSet.iInter fun _ ↦
      ((hσ k).measurableSet_eq_finite_before (hσ n).1 hF.complete_initial).compl
  let ρ (n : ℕ) := restrictedStoppingTime (σ n) (E n)
  have hρ (n : ℕ) : IsPredictableStoppingTime F (ρ n) P :=
    (hσ n).restrictedStoppingTime_before hF (hE n)
  have hg (n : ℕ) : stoppingTimeGraph (ρ n) =
      stoppingTimeGraph (σ n) ∩ (univ ×ˢ E n) :=
    stoppingTimeGraph_restricted (σ n) (E n)
  have hsub (n : ℕ) : stoppingTimeGraph (ρ n) ⊆ stoppingTimeGraph (σ n) := by
    rw [hg]
    exact inter_subset_left
  have hmem {n : ℕ} {p : ℝ≥0 × Ω} (hp : p ∈ stoppingTimeGraph (ρ n)) : p.2 ∈ E n := by
    rw [hg] at hp
    exact hp.2.2
  have hnodup {n m : ℕ} (hnm : n < m) {p : ℝ≥0 × Ω}
      (hn : p ∈ stoppingTimeGraph (ρ n)) (hm : p ∈ stoppingTimeGraph (ρ m)) : False := by
    have hEω := hmem hm
    have hn' : σ n p.2 = (p.1 : WithTop ℝ≥0) := hsub n hn
    have hm' : σ m p.2 = (p.1 : WithTop ℝ≥0) := hsub m hm
    exact hEω n hnm ⟨hn'.trans hm'.symm,
      fun htop ↦ WithTop.coe_ne_top (hm'.symm.trans htop)⟩
  refine ⟨ρ, hρ, hsub, ?_, ?_⟩
  · intro n m hnm
    apply Set.disjoint_left.mpr
    intro p hn hm
    rcases lt_or_gt_of_ne hnm with h | h
    · exact hnodup h hn hm
    · exact hnodup h hm hn
  · apply subset_antisymm (iUnion_mono hsub)
    intro p hp
    have hex : ∃ n, σ n p.2 = (p.1 : WithTop ℝ≥0) := by
      simpa only [mem_iUnion, mem_stoppingTimeGraph] using hp
    let n := Nat.find hex
    have hn : σ n p.2 = (p.1 : WithTop ℝ≥0) := Nat.find_spec hex
    have hEn : p.2 ∈ E n := by
      intro k hkn hk
      exact Nat.find_min hex hkn (hk.1.trans hn)
    apply mem_iUnion.mpr
    refine ⟨n, ?_⟩
    change restrictedStoppingTime (σ n) (E n) p.2 = (p.1 : WithTop ℝ≥0)
    rw [restrictedStoppingTime_of_mem (σ n) hEn]
    exact hn

/-- Removing zero-time graph points gives everywhere-positive predictable
times whose disjoint finite graphs cover precisely the original positive
finite graph union. Infinite lifetimes remain infinite and satisfy positivity. -/
theorem exists_positive_predictableStoppingTime_disjoint_graph_restrictions
    (σ : ℕ → Ω → WithTop ℝ≥0) (hσ : ∀ n, IsPredictableStoppingTime F (σ n) P)
    (hF : F.IsUsual P) :
    ∃ η : ℕ → Ω → WithTop ℝ≥0,
      (∀ n, IsPredictableStoppingTime F (η n) P) ∧
        (∀ n ω, 0 < η n ω) ∧
          (∀ n, stoppingTimeGraph (η n) ⊆ stoppingTimeGraph (σ n)) ∧
            Pairwise (fun n m ↦ Disjoint (stoppingTimeGraph (η n)) (stoppingTimeGraph (η m))) ∧
              (⋃ n, stoppingTimeGraph (η n)) =
                (Ioi 0 ×ˢ univ) ∩ ⋃ n, stoppingTimeGraph (σ n) := by
  classical
  obtain ⟨ρ, hρ, hsub, hd, hu⟩ :=
    exists_predictableStoppingTime_disjoint_graph_restrictions σ hσ hF
  let η (n : ℕ) := restrictedStoppingTime (ρ n) {ω | 0 < ρ n ω}
  have hη (n : ℕ) : IsPredictableStoppingTime F (η n) P :=
    (hρ n).restrictedStoppingTime_before hF
      ((hρ n).1.measurable_before measurableSet_Ioi)
  have hηsub (n : ℕ) : stoppingTimeGraph (η n) ⊆ stoppingTimeGraph (ρ n) := by
    rw [show stoppingTimeGraph (η n) =
      stoppingTimeGraph (ρ n) ∩ (univ ×ˢ {ω | 0 < ρ n ω}) from
        stoppingTimeGraph_restricted (ρ n) _]
    exact inter_subset_left
  have hηg (n : ℕ) : stoppingTimeGraph (η n) =
      (Ioi 0 ×ˢ univ) ∩ stoppingTimeGraph (ρ n) := by
    rw [show stoppingTimeGraph (η n) =
      stoppingTimeGraph (ρ n) ∩ (univ ×ˢ {ω | 0 < ρ n ω}) from
        stoppingTimeGraph_restricted (ρ n) _]
    ext p
    simp only [mem_inter_iff, mem_prod, mem_univ, true_and, and_true,
      mem_Ioi, mem_ofPred_eq, mem_stoppingTimeGraph]
    constructor
    · rintro ⟨he, hp⟩
      rw [he] at hp
      exact ⟨WithTop.coe_lt_coe.mp hp, he⟩
    · rintro ⟨hp, he⟩
      refine ⟨he, ?_⟩
      rw [he]
      exact WithTop.coe_lt_coe.mpr hp
  refine ⟨η, hη, ?_, fun n ↦ (hηsub n).trans (hsub n), ?_, ?_⟩
  · intro n ω
    change 0 < restrictedStoppingTime (ρ n) {ω | 0 < ρ n ω} ω
    by_cases hp : 0 < ρ n ω
    · rw [restrictedStoppingTime_of_mem (ρ n) hp]
      exact hp
    · rw [restrictedStoppingTime_of_notMem (ρ n) hp]
      exact WithTop.coe_lt_top 0
  · intro n m hnm
    exact (hd hnm).mono (hηsub n) (hηsub m)
  · calc
      _ = ⋃ n, (Ioi 0 ×ˢ univ) ∩ stoppingTimeGraph (ρ n) := iUnion_congr hηg
      _ = (Ioi 0 ×ˢ univ) ∩ ⋃ n, stoppingTimeGraph (ρ n) := by rw [inter_iUnion]
      _ = _ := by rw [hu]

end ProbabilityTheory
