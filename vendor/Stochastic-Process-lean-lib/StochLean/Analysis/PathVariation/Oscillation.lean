/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Analysis.PathVariation.Basic
public import Mathlib.Topology.UniformSpace.HeineCantor

/-! # Vanishing increments on fine deterministic partitions -/

@[expose] public section

open Filter Finset Set
open scoped NNReal Topology

namespace StochLean.TimePartition

variable {T : ℝ≥0}

theorem dist_right_left_eq_gap (π : TimePartition T) (i : Fin π.size) :
    dist (π.right i) (π.left i) = (π.gap i : ℝ) := by
  change |(π.right i : ℝ) - (π.left i : ℝ)| = (π.gap i : ℝ)
  rw [abs_of_nonneg (sub_nonneg.mpr (by exact_mod_cast π.left_le_right i))]
  exact (NNReal.coe_sub (π.left_le_right i)).symm

/-- Finite maximum increment, including the empty partition at zero. -/
noncomputable def maxIncrement (π : TimePartition T) (f : ℝ≥0 → ℝ) : ℝ≥0 :=
  Finset.univ.sup (fun i ↦ ‖π.increment f i‖₊)

theorem abs_increment_le_maxIncrement (π : TimePartition T) (f : ℝ≥0 → ℝ)
    (i : Fin π.size) : |π.increment f i| ≤ (π.maxIncrement f : ℝ) := by
  exact_mod_cast (Finset.le_sup (f := fun i ↦ ‖π.increment f i‖₊) (Finset.mem_univ i))

theorem maxIncrement_le (π : TimePartition T) {f : ℝ≥0 → ℝ} {δ : ℝ≥0}
    (h : ∀ i, |π.increment f i| ≤ δ) : π.maxIncrement f ≤ δ := by
  apply Finset.sup_le
  intro i _
  exact_mod_cast h i

/-- Uniform continuity on the compact horizon supplies one bound for every cell. -/
theorem maxIncrement_tendsto_zero {f : ℝ≥0 → ℝ} (hf : ContinuousOn f (Icc 0 T))
    {π : ℕ → TimePartition T}
    (hmesh : Tendsto (fun n ↦ ((π n).mesh : ℝ)) atTop (𝓝 0)) :
    Tendsto (fun n ↦ ((π n).maxIncrement f : ℝ)) atTop (𝓝 0) := by
  have huc := isCompact_Icc.uniformContinuousOn_of_continuous hf
  apply tendsto_order.mpr
  constructor
  · intro a ha
    exact Eventually.of_forall fun n ↦ ha.trans_le (NNReal.coe_nonneg _)
  · intro ε hε
    obtain ⟨η, hη, hmod⟩ := Metric.uniformContinuousOn_iff.mp huc (ε / 2) (by positivity)
    filter_upwards [hmesh.eventually_lt_const hη] with n hn
    have hinc : ∀ i, |(π n).increment f i| ≤ ε / 2 := by
      intro i
      apply le_of_lt
      apply hmod _ ⟨bot_le, (π n).point_le_horizon _⟩
        _ ⟨bot_le, (π n).point_le_horizon _⟩
      change dist ((π n).right i) ((π n).left i) < η
      rw [(π n).dist_right_left_eq_gap]
      exact (show ((π n).gap i : ℝ) ≤ ((π n).mesh : ℝ) by
        exact_mod_cast (π n).gap_le_mesh i).trans_lt hn
    have hb := (π n).maxIncrement_le (δ := ⟨ε / 2, by positivity⟩) hinc
    exact (show ((π n).maxIncrement f : ℝ) ≤ ε / 2 from
      NNReal.coe_le_coe.mpr hb).trans_lt (by linarith)

end StochLean.TimePartition
