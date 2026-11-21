/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.Semimartingale.SimplePredictable
public import StochLean.Probability.Process.Partition.Refinement
public import StochLean.Probability.Process.Stopping.CoefficientAtStopping
public import StochLean.Analysis.PathVariation.LeftStepApproximation

/-! # Repartitioning source simple predictable processes

The new coefficient is the old finite-step value immediately after the new left endpoint.
Its measurability is proved in that endpoint's stopping sigma-algebra. A genuine refinement
preserves the entire process and the elementary integral, including the independent time-zero
coefficient and all degenerate cells.
-/

@[expose] public section

open MeasureTheory Finset
open scoped NNReal

namespace ProbabilityTheory.SimplePredictableRep

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {F : Filtration ℝ≥0 mΩ}

theorem toProcess_eq_coefficient_of_mem_cell (H : SimplePredictableRep F) {t : ℝ≥0}
    {ω : Ω} {i : Fin H.partition.size}
    (hi : H.partition.point i.castSucc ω < t ∧ t ≤ H.partition.point i.succ ω) :
    H.toProcess t ω = H.coefficient i ω := by
  have ht : t ≠ 0 := ne_of_gt (lt_of_le_of_lt bot_le hi.1)
  rw [toProcess, if_neg ht, sum_eq_single i]
  · exact if_pos hi
  · intro j _ hji
    apply if_neg
    intro hj
    exact hji ((H.partition.path ω).cell_unique hj hi)
  · simp only [mem_univ, not_true_eq_false, false_implies]

theorem toProcess_eq_zero_of_terminal_lt (H : SimplePredictableRep F) {t : ℝ≥0}
    {ω : Ω} (ht : H.partition.terminal ω < t) : H.toProcess t ω = 0 := by
  have ht0 : t ≠ 0 := ne_of_gt (lt_of_le_of_lt bot_le ht)
  rw [toProcess, if_neg ht0]
  apply sum_eq_zero
  intro i _
  apply if_neg
  intro hi
  exact not_le_of_gt ht
    (hi.2.trans (H.partition.monotone_point ω (Fin.le_last i.succ)))

/-- Re-express coefficients on a proposed partition. Process preservation is established
below when the proposed partition actually refines the original one. -/
noncomputable def repartition (H : SimplePredictableRep F) (ρ : StoppingTimePartition F) :
    SimplePredictableRep F where
  partition := ρ
  initial := H.initial
  measurable_initial := H.measurable_initial
  coefficient := fun i ω ↦ ∑ j : Fin H.partition.size,
    if H.partition.point j.castSucc ω ≤ ρ.point i.castSucc ω ∧
        ρ.point i.castSucc ω < H.partition.point j.succ ω then H.coefficient j ω else 0
  measurable_coefficient := fun i ↦ Finset.measurable_fun_sum _ (fun j _ ↦
    (H.partition.point j.castSucc).measurable_right_interval_coefficient
      (H.partition.point j.succ) (ρ.point i.castSucc) (H.measurable_coefficient j))

@[simp] theorem partition_repartition (H : SimplePredictableRep F)
    (ρ : StoppingTimePartition F) : (H.repartition ρ).partition = ρ := rfl

theorem toProcess_repartition (H : SimplePredictableRep F) {ρ : StoppingTimePartition F}
    (hρ : ρ.Refines H.partition) : (H.repartition ρ).toProcess = H.toProcess := by
  funext t ω
  by_cases ht : t = 0
  · subst t
    simp only [toProcess_zero]
    rfl
  by_cases hterm : t ≤ ρ.terminal ω
  · have hcell : ∃ i : Fin ρ.size, ρ.point i.castSucc ω < t ∧ t ≤ ρ.point i.succ ω :=
      (ρ.path ω).exists_cell ⟨lt_of_le_of_ne bot_le (Ne.symm ht), hterm⟩
    obtain ⟨i, hi⟩ := hcell
    rw [(H.repartition ρ).toProcess_eq_coefficient_of_mem_cell (i := i) hi]
    change (∑ j : Fin H.partition.size,
      if H.partition.point j.castSucc ω ≤ ρ.point i.castSucc ω ∧
        ρ.point i.castSucc ω < H.partition.point j.succ ω then H.coefficient j ω else 0) = _
    rw [toProcess, if_neg ht]
    apply sum_congr rfl
    intro j _
    simp only [hρ.point_lt_iff_le_left hi j.castSucc, hρ.le_point_iff_left_lt hi j.succ]
  · have hρt : ρ.terminal ω < t := lt_of_not_ge hterm
    rw [(H.repartition ρ).toProcess_eq_zero_of_terminal_lt hρt,
      H.toProcess_eq_zero_of_terminal_lt ((hρ.terminal_le ω).trans_lt hρt)]

theorem integral_repartition (H : SimplePredictableRep F) {ρ : StoppingTimePartition F}
    (hρ : ρ.Refines H.partition) (X : ℝ≥0 → Ω → ℝ) :
    (H.repartition ρ).integral X = H.integral X :=
  (H.repartition ρ).integral_congr H (H.toProcess_repartition hρ) X

/-- Two source representations can be placed on exactly the same stopping partition,
without changing either process or adding coefficient bounds. -/
theorem exists_common_partition (H K : SimplePredictableRep F) :
    ∃ H' K' : SimplePredictableRep F, H'.partition = K'.partition ∧
      H'.toProcess = H.toProcess ∧ K'.toProcess = K.toProcess := by
  obtain ⟨ρ, hH, hK⟩ := H.partition.exists_common_refinement K.partition
  exact ⟨H.repartition ρ, K.repartition ρ, rfl,
    H.toProcess_repartition hH, K.toProcess_repartition hK⟩

end ProbabilityTheory.SimplePredictableRep
