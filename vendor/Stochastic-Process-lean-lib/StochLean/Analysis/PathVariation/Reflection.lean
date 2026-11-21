/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Analysis.PathVariation.Basic

/-! # Reflection of deterministic paths and invariance of square sums

There is no probability space in this layer. Flipping all increments of one interval preserves
every square sum whose partition contains both endpoints, including repeated endpoints.
-/

@[expose] public section

open Finset Set
open scoped NNReal

namespace StochLean

def reflectAfterPath (f : ℝ≥0 → ℝ) (a : ℝ≥0) : ℝ≥0 → ℝ :=
  fun t ↦ 2 * f (min t a) - f t

def flipIntervalPath (f : ℝ≥0 → ℝ) (a b : ℝ≥0) : ℝ≥0 → ℝ :=
  fun t ↦ f t - 2 * (f (min t b) - f (min t a))

theorem reflectAfterPath_eq_of_le (f : ℝ≥0 → ℝ) {a t : ℝ≥0} (ht : t ≤ a) :
    reflectAfterPath f a t = f t := by rw [reflectAfterPath, min_eq_left ht]; ring

theorem reflectAfterPath_eq_of_ge (f : ℝ≥0 → ℝ) {a t : ℝ≥0} (ht : a ≤ t) :
    reflectAfterPath f a t = 2 * f a - f t := by rw [reflectAfterPath, min_eq_right ht]

theorem reflectAfterPath_reflectAfterPath (f : ℝ≥0 → ℝ) {a b : ℝ≥0} (hab : a ≤ b) :
    reflectAfterPath (reflectAfterPath f a) b = flipIntervalPath f a b := by
  funext t
  simp only [reflectAfterPath, flipIntervalPath, min_assoc, min_eq_right hab]
  ring

theorem flipIntervalPath_eq_of_le (f : ℝ≥0 → ℝ) {a b t : ℝ≥0} (hab : a ≤ b)
    (ht : t ≤ a) : flipIntervalPath f a b t = f t := by
  rw [flipIntervalPath, min_eq_left (ht.trans hab), min_eq_left ht]
  ring

theorem flipIntervalPath_eq_of_mem (f : ℝ≥0 → ℝ) {a b t : ℝ≥0}
    (hat : a ≤ t) (htb : t ≤ b) : flipIntervalPath f a b t = 2 * f a - f t := by
  rw [flipIntervalPath, min_eq_left htb, min_eq_right hat]
  ring

theorem flipIntervalPath_eq_of_ge (f : ℝ≥0 → ℝ) {a b t : ℝ≥0} (hab : a ≤ b)
    (ht : b ≤ t) : flipIntervalPath f a b t = f t - 2 * (f b - f a) := by
  rw [flipIntervalPath, min_eq_right ht, min_eq_right (hab.trans ht)]

theorem continuous_reflectAfterPath {f : ℝ≥0 → ℝ} (hf : Continuous f) (a : ℝ≥0) :
    Continuous (reflectAfterPath f a) :=
  (continuous_const.mul (hf.comp (continuous_id.min continuous_const))).sub hf

theorem continuous_flipIntervalPath {f : ℝ≥0 → ℝ} (hf : Continuous f) (a b : ℝ≥0) :
    Continuous (flipIntervalPath f a b) :=
  hf.sub (continuous_const.mul ((hf.comp (continuous_id.min continuous_const)).sub
    (hf.comp (continuous_id.min continuous_const))))

/-- A partition endpoint cannot lie strictly inside any of its cells. -/
theorem TimePartition.endpoint_le_left_or_right_le {T : ℝ≥0} (π : TimePartition T)
    {a : ℝ≥0} (ha : a ∈ Set.range π.point) (i : Fin π.size) :
    a ≤ π.left i ∨ π.right i ≤ a := by
  obtain ⟨j, rfl⟩ := ha
  by_cases hj : j ≤ i.castSucc
  · exact Or.inl (π.monotone_point hj)
  · right
    apply π.monotone_point
    change i.val + 1 ≤ j.val
    exact Nat.succ_le_of_lt (lt_of_not_ge hj)

theorem TimePartition.increment_sq_flipIntervalPath {T : ℝ≥0} (π : TimePartition T)
    (f : ℝ≥0 → ℝ) {a b : ℝ≥0} (hab : a ≤ b)
    (ha : a ∈ Set.range π.point) (hb : b ∈ Set.range π.point) (i : Fin π.size) :
    (π.increment (flipIntervalPath f a b) i) ^ 2 = (π.increment f i) ^ 2 := by
  rcases π.endpoint_le_left_or_right_le ha i with hai | hia
  · rcases π.endpoint_le_left_or_right_le hb i with hbi | hib
    · rw [TimePartition.increment, TimePartition.increment,
        flipIntervalPath_eq_of_ge f hab (hbi.trans (π.left_le_right i)),
        flipIntervalPath_eq_of_ge f hab hbi]
      ring
    · rw [TimePartition.increment, TimePartition.increment,
        flipIntervalPath_eq_of_mem f (hai.trans (π.left_le_right i)) hib,
        flipIntervalPath_eq_of_mem f hai ((π.left_le_right i).trans hib)]
      ring
  · rw [TimePartition.increment, TimePartition.increment,
      flipIntervalPath_eq_of_le f hab hia,
      flipIntervalPath_eq_of_le f hab ((π.left_le_right i).trans hia)]

theorem quadraticVariationSum_flipIntervalPath {T : ℝ≥0} (π : TimePartition T)
    (f : ℝ≥0 → ℝ) {a b : ℝ≥0} (hab : a ≤ b)
    (ha : a ∈ Set.range π.point) (hb : b ∈ Set.range π.point) :
    quadraticVariationSum π (flipIntervalPath f a b) = quadraticVariationSum π f :=
  Finset.sum_congr rfl fun i _ ↦ π.increment_sq_flipIntervalPath f hab ha hb i

theorem TimePartition.increment_flipIntervalPath_self {T : ℝ≥0} (π : TimePartition T)
    (f : ℝ≥0 → ℝ) (i : Fin π.size) :
    π.increment (flipIntervalPath f (π.left i) (π.right i)) i = -π.increment f i := by
  rw [TimePartition.increment, TimePartition.increment,
    flipIntervalPath_eq_of_mem f (π.left_le_right i) le_rfl,
    flipIntervalPath_eq_of_mem f le_rfl (π.left_le_right i)]
  ring

theorem TimePartition.increment_flipIntervalPath_of_ne {T : ℝ≥0} (π : TimePartition T)
    (f : ℝ≥0 → ℝ) {i j : Fin π.size} (hij : i ≠ j) :
    π.increment (flipIntervalPath f (π.left i) (π.right i)) j = π.increment f j := by
  rcases lt_or_gt_of_ne hij with hij | hji
  · have hle : π.right i ≤ π.left j := π.monotone_point (by
      change i.val + 1 ≤ j.val
      exact Nat.succ_le_of_lt hij)
    rw [TimePartition.increment, TimePartition.increment,
      flipIntervalPath_eq_of_ge f (π.left_le_right i) (hle.trans (π.left_le_right j)),
      flipIntervalPath_eq_of_ge f (π.left_le_right i) hle]
    ring
  · have hle : π.right j ≤ π.left i := π.monotone_point (by
      change j.val + 1 ≤ i.val
      exact Nat.succ_le_of_lt hji)
    rw [TimePartition.increment, TimePartition.increment,
      flipIntervalPath_eq_of_le f (π.left_le_right i) hle,
      flipIntervalPath_eq_of_le f (π.left_le_right i) ((π.left_le_right j).trans hle)]

end StochLean
