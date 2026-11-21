/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.Partition

/-! # Finite capped partitions of an increasing stopping sequence

All `n` cells, including the first one, are retained. Stopping times may be infinite;
the finite cap gives everywhere-finite endpoints and repeated capped endpoints are legal.
-/

@[expose] public section

open MeasureTheory
open scoped NNReal

namespace ProbabilityTheory.StoppingTimePartition

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {F : Filtration ℝ≥0 mΩ}

noncomputable def truncateSequence (τ : ℕ → Ω → WithTop ℝ≥0)
    (hτ : ∀ n, IsStoppingTime F (τ n)) (hm : ∀ ω, Monotone (τ · ω))
    (h0 : ∀ ω, τ 0 ω = 0) (n : ℕ) (T : ℝ≥0) : StoppingTimePartition F where
  size := n
  point := fun i ↦ FiniteStoppingTime.truncate (hτ i) T
  monotone_point := by
    intro ω i j hij
    apply WithTop.coe_le_coe.mp
    change (FiniteStoppingTime.truncate (hτ i) T).withTop ω ≤
      (FiniteStoppingTime.truncate (hτ j) T).withTop ω
    rw [FiniteStoppingTime.withTop_truncate, FiniteStoppingTime.withTop_truncate]
    exact min_le_min_left _ (hm ω hij)
  first_eq_zero := by
    intro ω
    apply WithTop.coe_eq_coe.mp
    change (FiniteStoppingTime.truncate (hτ 0) T).withTop ω = (0 : WithTop ℝ≥0)
    rw [FiniteStoppingTime.withTop_truncate]
    change min (T : WithTop ℝ≥0) (τ 0 ω) = (0 : WithTop ℝ≥0)
    rw [h0 ω]
    exact min_eq_right (WithTop.coe_le_coe.mpr (show (0 : ℝ≥0) ≤ T from bot_le))

variable (τ : ℕ → Ω → WithTop ℝ≥0) (hτ : ∀ n, IsStoppingTime F (τ n))
  (hm : ∀ ω, Monotone (τ · ω)) (h0 : ∀ ω, τ 0 ω = 0) (n : ℕ) (T : ℝ≥0)

@[simp] theorem coe_truncateSequence_point (i : Fin (n + 1)) (ω : Ω) :
    ((truncateSequence τ hτ hm h0 n T).point i ω : WithTop ℝ≥0) =
      min (T : WithTop ℝ≥0) (τ i ω) :=
  congrFun (FiniteStoppingTime.withTop_truncate (hτ i) T) ω

theorem truncateSequence_point_le (i : Fin (n + 1)) (ω : Ω) :
    (truncateSequence τ hτ hm h0 n T).point i ω ≤ T :=
  FiniteStoppingTime.truncate_le (hτ i) T ω

theorem coe_truncateSequence_point_le_original (i : Fin (n + 1)) (ω : Ω) :
    ((truncateSequence τ hτ hm h0 n T).point i ω : WithTop ℝ≥0) ≤ τ i ω := by
  rw [coe_truncateSequence_point]
  exact min_le_right _ _

theorem coe_truncateSequence_terminal (ω : Ω) :
    ((truncateSequence τ hτ hm h0 n T).terminal ω : WithTop ℝ≥0) =
      min (T : WithTop ℝ≥0) (τ n ω) :=
  coe_truncateSequence_point τ hτ hm h0 n T (Fin.last n) ω

theorem le_truncateSequence_terminal {t : ℝ≥0} {ω : Ω}
    (ht : t ≤ T) (hτt : (t : WithTop ℝ≥0) ≤ τ n ω) :
    t ≤ (truncateSequence τ hτ hm h0 n T).terminal ω := by
  apply WithTop.coe_le_coe.mp
  rw [coe_truncateSequence_terminal]
  exact le_min (WithTop.coe_le_coe.mpr ht) hτt

theorem original_eq_truncateSequence_point_of_lt {i : Fin (n + 1)} {ω : Ω}
    (hi : (truncateSequence τ hτ hm h0 n T).point i ω < T) :
    τ i ω = ((truncateSequence τ hτ hm h0 n T).point i ω : WithTop ℝ≥0) := by
  have hmin : min (T : WithTop ℝ≥0) (τ i ω) < (T : WithTop ℝ≥0) := by
    rw [← coe_truncateSequence_point τ hτ hm h0 n T i ω]
    exact WithTop.coe_lt_coe.mpr hi
  have hlt : τ i ω < (T : WithTop ℝ≥0) :=
    (min_lt_iff.mp hmin).resolve_left (lt_irrefl _)
  rw [coe_truncateSequence_point, min_eq_right hlt.le]

end ProbabilityTheory.StoppingTimePartition
