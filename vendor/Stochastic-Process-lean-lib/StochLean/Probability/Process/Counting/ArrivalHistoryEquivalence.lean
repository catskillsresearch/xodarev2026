/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.Counting.ArrivalInterarrival
public import Mathlib.Algebra.BigOperators.Fin

/-! # Actual finite arrival and interarrival histories contain the same information

For an everywhere-valid arrival sequence, the first `n` arrivals and the
first `n` actual interarrival durations generate exactly the same sigma
algebra. Each gap depends measurably on its current and previous arrival,
and the actual prefix-sum theorem measurably recovers each arrival.

Finite vectors are extended by infinity only inside a local proof expression
used to apply the existing measurable-gap theorem. Every queried coordinate
and its predecessor are inside the original finite vector. There is no new
history, arrival, count or conditional-distribution owner.

The two measurable transformations factor the actual histories. They are
not asserted to be inverse transformations on the whole ambient vector
space: arbitrary latent gaps following infinity are not actual absorbing
gaps. The result also makes no pointwise identification of conditional
distribution kernels. No probability or ambient measurability assumption
is needed, and the zero-length history is genuinely empty.
-/

@[expose] public section

open MeasureTheory
open scoped NNReal ENNReal

namespace ProbabilityTheory.IsNonexplosiveArrivalSequence

/-- Finite histories of the original arrivals and their actual absorbing
interarrival durations generate exactly the same sigma algebra. Validity
is everywhere; an almost-everywhere path guard alone would not justify an
equality of the raw, uncompleted sigma algebras. -/
theorem comap_arrival_history_eq_interarrival_history
    {Ω : Type*} {Γ : ℕ → Ω → WithTop ℝ≥0}
    (hΓ : ∀ ω, IsNonexplosiveArrivalSequence (fun k ↦ Γ k ω)) (n : ℕ) :
    MeasurableSpace.comap (fun ω (i : Fin n) ↦ Γ i ω) inferInstance =
      MeasurableSpace.comap
        (fun ω (i : Fin n) ↦ arrivalInterarrival (fun k ↦ Γ k ω) i) inferInstance := by
  classical
  let A : Ω → Fin n → WithTop ℝ≥0 := fun ω i ↦ Γ i ω
  let G : Ω → Fin n → WithTop ℝ≥0 :=
    fun ω i ↦ arrivalInterarrival (fun k ↦ Γ k ω) i
  let D : (Fin n → WithTop ℝ≥0) → Fin n → WithTop ℝ≥0 := fun z i ↦
    arrivalInterarrival (fun k ↦ if hk : k < n then z ⟨k, hk⟩ else ⊤) i
  let R : (Fin n → WithTop ℝ≥0) → Fin n → WithTop ℝ≥0 := fun z i ↦
    ∑ j : Fin (i.val + 1), z (Fin.castLE (Nat.succ_le_of_lt i.isLt) j)
  have hDmeas : Measurable D := by
    refine measurable_pi_lambda _ fun i ↦ ?_
    apply measurable_arrivalInterarrival
    intro k
    by_cases hk : k < n
    · simpa only [dif_pos hk] using
        (measurable_pi_apply (⟨k, hk⟩ : Fin n) :
          Measurable (fun z : Fin n → WithTop ℝ≥0 ↦ z ⟨k, hk⟩))
    · simpa only [dif_neg hk] using
        (measurable_const : Measurable (fun _ : Fin n → WithTop ℝ≥0 ↦ ⊤))
  have hRmeas : Measurable R := by
    let : MeasurableAdd₂ (WithTop ℝ≥0) := inferInstanceAs (MeasurableAdd₂ ℝ≥0∞)
    refine measurable_pi_lambda _ fun i ↦ ?_
    exact Finset.univ.measurable_fun_sum fun j _ ↦
      measurable_pi_apply (Fin.castLE (Nat.succ_le_of_lt i.isLt) j)
  have hD : G = D ∘ A := by
    funext ω i
    change arrivalInterarrival (fun k ↦ Γ k ω) i.val =
      arrivalInterarrival (fun k ↦ if _hk : k < n then Γ k ω else ⊤) i.val
    rcases i with ⟨k, hk⟩
    cases k with
    | zero => simp only [arrivalInterarrival, dif_pos hk]
    | succ k =>
        have hk' : k < n := (Nat.lt_succ_self k).trans hk
        simp only [arrivalInterarrival, dif_pos hk, dif_pos hk']
  have hR : A = R ∘ G := by
    funext ω i
    change Γ i ω = ∑ j : Fin (i.val + 1), arrivalInterarrival (fun k ↦ Γ k ω) j
    rw [Fin.sum_univ_eq_sum_range]
    exact ((hΓ ω).arrivalInterarrival_properties.2.1 i).symm
  exact le_antisymm
    (MeasurableSpace.comap_le_comap_of_eq_comp R hRmeas hR)
    (MeasurableSpace.comap_le_comap_of_eq_comp D hDmeas hD)

end ProbabilityTheory.IsNonexplosiveArrivalSequence
