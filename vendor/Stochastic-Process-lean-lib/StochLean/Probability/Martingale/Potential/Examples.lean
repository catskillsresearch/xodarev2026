/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Martingale.Potential.Basic

/-! # Potentials with arbitrary integrable initial data -/

@[expose] public section

open MeasureTheory Filter
open scoped Topology

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsFiniteMeasure P]
  {F : Filtration ℕ mΩ} {V : Ω → ℝ}

theorem isPotential_singleDrop (hm : StronglyMeasurable[F 0] V)
    (hi : Integrable V P) (hn : ∀ᵐ ω ∂P, 0 ≤ V ω) :
    IsPotential (fun n : ℕ ↦ if n = 0 then V else 0) F P := by
  have ha : StronglyAdapted F (fun n : ℕ ↦ if n = 0 then V else 0) := by
    intro n
    by_cases h : n = 0
    · subst n
      simpa using hm
    · simpa only [if_neg h] using (stronglyMeasurable_zero : StronglyMeasurable[F n] (0 : Ω → ℝ))
  have hiX (n : ℕ) : Integrable (if n = 0 then V else 0) P := by
    by_cases h : n = 0
    · simpa only [if_pos h] using hi
    · simpa only [if_neg h] using (integrable_zero Ω ℝ P)
  refine ⟨⟨ha, fun i j hij ↦ ?_, hiX⟩, ?_, ?_⟩
  · change P[(if j = 0 then V else 0) | F i] ≤ᵐ[P] (if i = 0 then V else 0)
    by_cases hj : j = 0
    · subst j
      have h : i = 0 := Nat.eq_zero_of_le_zero hij
      subst i
      rw [if_pos rfl, condExp_of_stronglyMeasurable (F.le 0) hm hi]
    · rw [if_neg hj, condExp_zero]
      by_cases hi : i = 0
      · rw [if_pos hi]
        exact hn
      · rw [if_neg hi]
  · intro n
    by_cases h : n = 0
    · simpa only [if_pos h] using hn
    · simp [h]
  · apply tendsto_atTop_of_eventually_const (i₀ := 1)
    intro n hn
    have hne : n ≠ 0 := Nat.ne_zero_of_lt hn
    simp only [if_neg hne, Pi.zero_apply, integral_zero]

end ProbabilityTheory
