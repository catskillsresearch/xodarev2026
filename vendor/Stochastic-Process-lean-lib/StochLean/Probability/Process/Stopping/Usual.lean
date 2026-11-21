/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.Filtration.Usual
public import Mathlib.Probability.Process.Stopping

/-! # Stopping times and null-set changes under usual conditions -/

@[expose] public section

open MeasureTheory Filter Set
open scoped NNReal

namespace MeasureTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
  {F : Filtration ℝ≥0 mΩ}

theorem IsStoppingTime.congr_ae_of_usual {τ σ : Ω → WithTop ℝ≥0}
    (hτ : IsStoppingTime F τ) (hF : F.IsUsual P) (heq : τ =ᵐ[P] σ) :
    IsStoppingTime F σ := by
  intro t
  have hc : IsCompleteSubMeasurableSpace P (F t) := fun s hs ↦
    F.mono bot_le s (hF.complete_initial s hs)
  let : MeasurableSpace Ω := F t
  apply measurableSet_setOfPred.mpr
  apply hc.measurable_congr_ae (measurableSet_setOfPred.mp (hτ t))
  filter_upwards [heq] with ω hω
  exact congrArg (fun s ↦ s ≤ (t : WithTop ℝ≥0)) hω

/-- An AE-monotone source sequence has an everywhere-monotone stopping-time version.
All coordinates agree simultaneously off one initial null event. -/
theorem exists_monotone_stoppingSequence_version {τ : ℕ → Ω → WithTop ℝ≥0}
    (hF : F.IsUsual P) (hτ : ∀ n, IsStoppingTime F (τ n))
    (hmono : ∀ᵐ ω ∂P, Monotone (τ · ω)) :
    ∃ σ : ℕ → Ω → WithTop ℝ≥0, Monotone σ ∧ (∀ n, IsStoppingTime F (σ n)) ∧
      (∀ n, σ n ≤ τ n) ∧ (∀ᵐ ω ∂P, ∀ n, τ n ω = σ n ω) := by
  classical
  let σ : ℕ → Ω → WithTop ℝ≥0 := fun n ω ↦ if Monotone (τ · ω) then τ n ω else 0
  have heq : ∀ᵐ ω ∂P, ∀ n, τ n ω = σ n ω := by
    filter_upwards [hmono] with ω hω n
    exact (if_pos hω).symm
  refine ⟨σ, ?_, fun n ↦ (hτ n).congr_ae_of_usual hF (heq.mono fun _ hω ↦ hω n), ?_, heq⟩
  · intro n m hnm ω
    by_cases hω : Monotone (τ · ω)
    · simpa only [σ, if_pos hω] using hω hnm
    · simp only [σ, if_neg hω, le_refl]
  · intro n ω
    dsimp only [σ]
    split_ifs
    · exact le_rfl
    · exact bot_le

end MeasureTheory
