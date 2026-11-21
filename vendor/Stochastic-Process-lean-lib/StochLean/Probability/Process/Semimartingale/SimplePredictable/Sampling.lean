/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.Semimartingale.SimplePredictable.Normalization
public import StochLean.Probability.Process.Partition.Sampling
public import StochLean.Probability.Martingale.DiscreteIntegral.L2

/-! # The elementary integral as an existing discrete predictable integral

The coefficient at index `n + 1` is measurable at the original left stopping endpoint, even
when the integrator is stopped at a deterministic horizon. No deterministic bound on the
partition endpoints, or change to their sigma-fields, is imposed.
-/

@[expose] public section

open MeasureTheory Finset
open scoped NNReal ENNReal BigOperators

namespace ProbabilityTheory.SimplePredictableRep

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {F : Filtration ℝ≥0 mΩ}

def discreteCoefficient (H : SimplePredictableRep F) : ℕ → Ω → ℝ
  | 0 => 0
  | n + 1 => if hn : n < H.partition.size then H.coefficient ⟨n, hn⟩ else 0

@[simp] theorem discreteCoefficient_zero (H : SimplePredictableRep F) :
    H.discreteCoefficient 0 = 0 := rfl

theorem discreteCoefficient_fin (H : SimplePredictableRep F) (i : Fin H.partition.size) :
    H.discreteCoefficient (i + 1) = H.coefficient i := by
  simp only [discreteCoefficient, dif_pos i.isLt]

theorem stronglyPredictable_discreteCoefficient (H : SimplePredictableRep F) :
    IsStronglyPredictable H.partition.sampledFiltration H.discreteCoefficient := by
  apply IsStronglyPredictable.of_measurable_add_one stronglyMeasurable_zero
  intro n
  by_cases hn : n < H.partition.size
  · simp only [discreteCoefficient, dif_pos hn]
    change StronglyMeasurable[(H.partition.pointNat n).measurableSpace]
      (H.coefficient ⟨n, hn⟩)
    have hp : H.partition.pointNat n = H.partition.point (Fin.castSucc ⟨n, hn⟩) :=
      H.partition.pointNat_fin (Fin.castSucc ⟨n, hn⟩)
    rw [hp]
    exact (H.measurable_coefficient ⟨n, hn⟩).stronglyMeasurable
  · simp only [discreteCoefficient, dif_neg hn]
    exact stronglyMeasurable_zero

theorem norm_discreteCoefficient_le (H : SimplePredictableRep F) {C : ℝ}
    (hC : 0 ≤ C) (hb : ∀ i ω, ‖H.coefficient i ω‖ ≤ C) (n : ℕ) (ω : Ω) :
    ‖H.discreteCoefficient n ω‖ ≤ C := by
  cases n with
  | zero => simpa only [discreteCoefficient_zero, Pi.zero_apply, norm_zero] using hC
  | succ n =>
    by_cases hn : n < H.partition.size
    · simpa only [discreteCoefficient, dif_pos hn] using hb ⟨n, hn⟩ ω
    · simpa only [discreteCoefficient, dif_neg hn, Pi.zero_apply, norm_zero] using hC

theorem integral_eq_initial_add_discreteStochasticIntegral (H : SimplePredictableRep F)
    (X : ℝ≥0 → Ω → ℝ) :
    H.integral X = fun ω ↦ H.initial ω * X 0 ω +
      discreteStochasticIntegral H.discreteCoefficient (H.partition.sampledProcess X)
        H.partition.size ω := by
  funext ω
  rw [integral, discreteStochasticIntegral, ← Fin.sum_univ_eq_sum_range]
  congr 1
  apply sum_congr rfl
  intro i _
  rw [H.discreteCoefficient_fin i]
  have hl : H.partition.pointNat i = H.partition.point i.castSucc :=
    H.partition.pointNat_fin i.castSucc
  have hr : H.partition.pointNat (i + 1) = H.partition.point i.succ :=
    H.partition.pointNat_fin i.succ
  simp only [StoppingTimePartition.sampledProcess, hl, hr, smul_eq_mul]

end ProbabilityTheory.SimplePredictableRep
