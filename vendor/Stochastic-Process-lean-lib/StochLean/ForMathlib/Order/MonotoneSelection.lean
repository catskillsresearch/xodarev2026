/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import Mathlib.Order.Monotone.Basic
public import Mathlib.Order.Interval.Set.Basic

/-! # Monotone selection with a different predicate at each index

If each requested predicate has a witness between a boundary and every point
on its chosen side, all predicates can be realized by one strictly monotone
sequence on that side. No topology or numerical shrinking rate is required.
-/

@[expose] public section

theorem exists_strictAnti_seq_of_between
    {α : Type*} [Preorder α] {t B : α} {p : ℕ → α → Prop} (hB : t < B)
    (h : ∀ n y, t < y → ∃ z, t < z ∧ z < y ∧ p n z) :
    ∃ u : ℕ → α, StrictAnti u ∧ ∀ n, t < u n ∧ u n < B ∧ p n (u n) := by
  classical
  choose next hnext using fun n (y : Set.Ioi t) ↦ h n y y.property
  let start : Set.Ioi t := ⟨B, hB⟩
  let step (n : ℕ) (y : Set.Ioi t) : Set.Ioi t := ⟨next n y, (hnext n y).1⟩
  let v : ℕ → Set.Ioi t := Nat.rec (step 0 start) (fun n y ↦ step (n + 1) y)
  let u : ℕ → α := fun n ↦ (v n).val
  have hs (n) : u (n + 1) < u n := (hnext (n + 1) (v n)).2.1
  have ha : StrictAnti u := strictAnti_nat_of_succ_lt hs
  have hzero : u 0 < B := (hnext 0 start).2.1
  refine ⟨u, ha, fun n ↦ ⟨(v n).property, (ha.antitone (Nat.zero_le n)).trans_lt hzero, ?_⟩⟩
  cases n with
  | zero => exact (hnext 0 start).2.2
  | succ n => exact (hnext (n + 1) (v n)).2.2

theorem exists_strictMono_seq_of_between
    {α : Type*} [Preorder α] {B t : α} {p : ℕ → α → Prop} (hB : B < t)
    (h : ∀ n y, y < t → ∃ z, z < t ∧ y < z ∧ p n z) :
    ∃ u : ℕ → α, StrictMono u ∧ ∀ n, u n < t ∧ B < u n ∧ p n (u n) :=
  exists_strictAnti_seq_of_between (α := αᵒᵈ) hB h
