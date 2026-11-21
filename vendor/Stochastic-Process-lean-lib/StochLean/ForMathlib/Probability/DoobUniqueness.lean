/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import Mathlib.Probability.Martingale.Centering
public import StochLean.Probability.Process.Equivalence

/-! # Discrete Doob uniqueness with AE decomposition and initial normalization

Predictable differences are martingales by transport from the martingale
parts. A predictable discrete martingale is constant; an AE-zero initial
value suffices. No raw process equality or completed filtration is required.
-/

@[expose] public section

open ProbabilityTheory Filter

namespace MeasureTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
  {F : Filtration ℕ mΩ} [SigmaFiniteFiltration P F]
  {X M N A B : ℕ → Ω → ℝ}

theorem doob_decomposition_indistinguishable (hM : Martingale M F P)
    (hN : Martingale N F P) (hA : IsStronglyPredictable F A)
    (hB : IsStronglyPredictable F B) (hA0 : A 0 =ᵐ[P] 0) (hB0 : B 0 =ᵐ[P] 0)
    (hXA : IsModification X (M - A) P) (hXB : IsModification X (N - B) P) :
    Indistinguishable M N P ∧ Indistinguishable A B P := by
  have he : IsModification (M - N) (A - B) P := by
    intro n
    filter_upwards [hXA n, hXB n] with ω ha hb
    change X n ω = M n ω - A n ω at ha
    change X n ω = N n ω - B n ω at hb
    change M n ω - N n ω = A n ω - B n ω
    linarith
  have hD : Martingale (A - B) F P :=
    (hM.sub hN).congr (hA.stronglyAdapted.sub hB.stronglyAdapted) he
  have hpred : StronglyAdapted F (fun n ↦ (A - B) (n + 1)) :=
    fun n ↦ (hA.measurable_add_one n).sub (hB.measurable_add_one n)
  have hz : (A - B) 0 =ᵐ[P] 0 := by
    change A 0 - B 0 =ᵐ[P] 0
    simpa only [sub_zero] using hA0.sub hB0
  have hAB : IsModification A B P := by
    intro n
    filter_upwards [(hD.eq_zero_of_predictable hpred n).trans hz] with ω hω
    exact sub_eq_zero.mp hω
  have hMN : IsModification M N P := by
    intro n
    filter_upwards [he n, hAB n] with ω heω habω
    change M n ω - N n ω = A n ω - B n ω at heω
    rw [habω, sub_self] at heω
    exact sub_eq_zero.mp heω
  exact ⟨hMN.indistinguishable_of_countable, hAB.indistinguishable_of_countable⟩

end MeasureTheory
