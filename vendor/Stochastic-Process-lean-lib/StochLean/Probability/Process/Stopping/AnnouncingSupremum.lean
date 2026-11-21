/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.Stopping.AnnouncingStability
public import StochLean.Probability.Process.Stopping.Supremum

/-! # Countable suprema of predictable times

Finite maxima of capped announcing terms give a single increasing announcing
sequence for the supremum. Only countably many convergence events are combined;
strict inequalities and monotonicity remain pointwise. This does not extend to
decreasing limits of predictable stopping times.
-/

@[expose] public section

open MeasureTheory Filter Finset
open scoped NNReal Topology

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {F : Filtration ℝ≥0 mΩ} {P : Measure Ω}

theorem IsPredictableStoppingTime.iSup_nat {τ : ℕ → Ω → WithTop ℝ≥0}
    (hτ : ∀ i, IsPredictableStoppingTime F (τ i) P) :
    IsPredictableStoppingTime F (fun ω ↦ ⨆ i, τ i ω) P := by
  choose σ hs hle using fun i ↦ (hτ i).exists_announcing_le
  let π (n : ℕ) (ω : Ω) := (range (n + 1)).sup (fun i ↦ σ i n ω)
  have hmono (ω : Ω) : Monotone (fun n ↦ π n ω) := by
    intro n m hnm
    apply Finset.sup_le_iff.mpr
    intro i hi
    exact ((hs i).monotone ω hnm).trans
      (Finset.le_sup (f := fun i ↦ σ i m ω) (mem_range.mpr
        (lt_of_lt_of_le (mem_range.mp hi) (Nat.add_le_add_right hnm 1))))
  have hupper (n : ℕ) (ω : Ω) : π n ω ≤ ⨆ i, τ i ω := by
    apply Finset.sup_le_iff.mpr
    intro i _
    exact (hle i n ω).trans (le_iSup (fun j ↦ τ j ω) i)
  refine ⟨IsStoppingTime.iSup_nnreal (fun i ↦ (hτ i).1), π,
    fun n ↦ IsStoppingTime.finset_sup_nnreal (range (n + 1))
      (fun i _ ↦ (hs i).isStoppingTime n), hmono, fun n ω ht ↦ ?_, ?_⟩
  · apply (Finset.sup_lt_iff ht).mpr
    intro i _
    by_cases hpos : 0 < τ i ω
    · exact ((hs i).strict n ω hpos).trans_le (le_iSup (fun j ↦ τ j ω) i)
    · have hz : τ i ω = 0 := le_antisymm (le_of_not_gt hpos) bot_le
      have hzero : σ i n ω = 0 := le_antisymm (hz ▸ hle i n ω) bot_le
      simpa only [hzero] using ht
  · filter_upwards [ae_all_iff.mpr (fun i ↦ (hs i).tendsto)] with ω hl
    have he : (⨆ n, π n ω) = ⨆ i, τ i ω := by
      apply le_antisymm (iSup_le (fun n ↦ hupper n ω))
      apply iSup_le
      intro i
      apply le_of_tendsto (hl i)
      filter_upwards [eventually_ge_atTop i] with n hn
      exact (Finset.le_sup (f := fun j ↦ σ j n ω)
        (mem_range.mpr (Nat.lt_succ_of_le hn))).trans (le_iSup (fun n ↦ π n ω) n)
    rw [← he]
    exact tendsto_atTop_iSup (hmono ω)

end ProbabilityTheory
