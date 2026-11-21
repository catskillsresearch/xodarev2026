/-
Copyright (c) 2025 Cameron Freer. All rights reserved.
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer, StochLean contributors
-/
module

public import Mathlib.Probability.Martingale.Upcrossing

/-! # Finite-prefix congruence for native crossing times

Adapted from the audited project-internal exchangeability pathwise proof.
Only the native Mathlib crossing owners are used. The closed prefix includes
the cutoff because the underlying bounded hitting search includes it.
-/

@[expose] public section

namespace MeasureTheory

theorem hittingBtwn_congr_on_Icc
    {Ω β : Type*} {u v : ℕ → Ω → β} {s : Set β} {n m : ℕ} {ω : Ω}
    (h : ∀ k, n ≤ k → k ≤ m → u k ω = v k ω) :
    hittingBtwn u s n m ω = hittingBtwn v s n m ω := by
  have he : {k | k ∈ Set.Icc n m ∧ u k ω ∈ s} =
      {k | k ∈ Set.Icc n m ∧ v k ω ∈ s} := by
    ext k
    by_cases hk : k ∈ Set.Icc n m
    · simp only [Set.mem_ofPred_eq, hk, true_and, h k hk.1 hk.2]
    · simp only [Set.mem_ofPred_eq, hk, false_and]
  have hex : (∃ k ∈ Set.Icc n m, u k ω ∈ s) ↔ ∃ k ∈ Set.Icc n m, v k ω ∈ s := by
    change ({k | k ∈ Set.Icc n m ∧ u k ω ∈ s}).Nonempty ↔
      ({k | k ∈ Set.Icc n m ∧ v k ω ∈ s}).Nonempty
    rw [he]
  simp only [hittingBtwn]
  split_ifs with hu hv hv
  · exact congrArg sInf he
  · exact (hv (hex.mp hu)).elim
  · exact (hu (hex.mpr hv)).elim
  · rfl

theorem upperCrossingTime_congr_on_Iic
    {Ω : Type*} {a b : ℝ} {f g : ℕ → Ω → ℝ} {N : ℕ} {ω : Ω}
    (h : ∀ n ≤ N, f n ω = g n ω) (k : ℕ) :
    upperCrossingTime a b f N k ω = upperCrossingTime a b g N k ω := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [upperCrossingTime_succ_eq, upperCrossingTime_succ_eq]
    have hl : lowerCrossingTime a b f N k ω = lowerCrossingTime a b g N k ω := by
      simp only [lowerCrossingTime]
      rw [ih]
      exact hittingBtwn_congr_on_Icc (fun n _ hn ↦ h n hn)
    rw [hl]
    exact hittingBtwn_congr_on_Icc (fun n _ hn ↦ h n hn)

theorem upcrossingsBefore_congr_on_Iic
    {Ω : Type*} {a b : ℝ} {f g : ℕ → Ω → ℝ} {N : ℕ} {ω : Ω}
    (h : ∀ n ≤ N, f n ω = g n ω) :
    upcrossingsBefore a b f N ω = upcrossingsBefore a b g N ω := by
  simp only [upcrossingsBefore, upperCrossingTime_congr_on_Iic h]

end MeasureTheory
