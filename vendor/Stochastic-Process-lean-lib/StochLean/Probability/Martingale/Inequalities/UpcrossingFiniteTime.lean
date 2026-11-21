/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.Filtration.SubmartingaleReindex
public import StochLean.Analysis.PathVariation.Approximation
public import Mathlib.Probability.Martingale.Upcrossing

/-! # Upcrossing estimates on arbitrary finite time partitions

The discrete upcrossing owner is evaluated strictly before `size + 1`, so
the last sample at the terminal horizon is included. Monotone sampling uses
the canonical reindexed filtration. The bounds need only first moments and
no path regularity; they are prerequisites for general continuous-time
submartingale convergence, not a claim of that full limit theorem.
-/

@[expose] public section

open StochLean Filter
open scoped NNReal ENNReal

namespace MeasureTheory.Submartingale

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsFiniteMeasure P]
  {F : Filtration ℝ≥0 mΩ} {X : ℝ≥0 → Ω → ℝ} {T : ℝ≥0} {a b : ℝ}

omit [IsFiniteMeasure P] in
theorem measurable_upcrossings_partition (hX : Submartingale X F P)
    (hab : a < b) (π : TimePartition T) :
    Measurable (upcrossingsBefore a b (fun n ↦ X (π.pointNat n)) (π.size + 1)) :=
  (hX.reindex π.pointNat π.pointNat_mono).stronglyAdapted.measurable_upcrossingsBefore hab

theorem integrable_upcrossings_partition (hX : Submartingale X F P)
    (hab : a < b) (π : TimePartition T) :
    Integrable (fun ω ↦
      (upcrossingsBefore a b (fun n ↦ X (π.pointNat n)) (π.size + 1) ω : ℝ)) P :=
  (hX.reindex π.pointNat π.pointNat_mono).stronglyAdapted.integrable_upcrossingsBefore hab

theorem mul_integral_upcrossings_partition_le (hX : Submartingale X F P)
    (a b : ℝ) (π : TimePartition T) :
    (b - a) * (∫ ω,
      (upcrossingsBefore a b (fun n ↦ X (π.pointNat n)) (π.size + 1) ω : ℝ) ∂P) ≤
        ∫ ω, (X T ω - a)⁺ ∂P := by
  have ht : π.pointNat (π.size + 1) = T := by
    simp only [TimePartition.pointNat, min_eq_right (Nat.le_succ _)]
    exact π.last_eq_horizon
  simpa only [ht] using Submartingale.mul_integral_upcrossingsBefore_le_integral_pos_part
    a b (hX.reindex π.pointNat π.pointNat_mono) (π.size + 1)

/-- The endpoint first moment bounds crossings uniformly over all finite
partitions. The level correction is scaled by the measure's total mass. -/
theorem mul_integral_upcrossings_partition_le_firstMoment (hX : Submartingale X F P)
    (a b : ℝ) (π : TimePartition T) :
    (b - a) * (∫ ω,
      (upcrossingsBefore a b (fun n ↦ X (π.pointNat n)) (π.size + 1) ω : ℝ) ∂P) ≤
        (∫ ω, ‖X T ω‖ ∂P) + P.real Set.univ * |a| := by
  apply (hX.mul_integral_upcrossings_partition_le a b π).trans
  calc
    _ ≤ ∫ ω, ‖X T ω‖ + |a| ∂P := by
      apply integral_mono_of_nonneg (Eventually.of_forall fun _ ↦ posPart_nonneg _)
        ((hX.integrable T).norm.add (integrable_const |a|))
      filter_upwards with ω
      change (X T ω - a)⁺ ≤ ‖X T ω‖ + |a|
      rw [posPart_def, Real.norm_eq_abs]
      apply max_le
      · linarith [le_abs_self (X T ω), neg_le_abs a]
      · positivity
    _ = _ := by
      rw [integral_add (hX.integrable T).norm (integrable_const |a|), integral_const]
      rfl

end MeasureTheory.Submartingale
