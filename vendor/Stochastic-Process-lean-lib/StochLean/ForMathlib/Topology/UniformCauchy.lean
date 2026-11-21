/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import Mathlib.Topology.MetricSpace.UniformConvergence
public import Mathlib.Topology.MetricSpace.Cauchy
public import Mathlib.Analysis.SpecificLimits.Basic

/-! # Uniform Cauchy control from eventually geometric increments

Mathlib's complete extended-metric uniform function space supplies the Cauchy
argument. No boundedness of the functions or of their initial differences is needed.
-/

@[expose] public section

open Filter Set
open scoped Topology ENNReal UniformConvergence

theorem uniformCauchySeqOn_of_eventually_geometric {α E : Type*}
    [MetricSpace E] [CompleteSpace E] {F : ℕ → α → E} {s : Set α}
    (h : ∀ᶠ n in atTop, ∀ x ∈ s,
      edist (F n x) (F (n + 1) x) ≤ (2⁻¹ : ℝ≥0∞) ^ n) :
    UniformCauchySeqOn F atTop s := by
  obtain ⟨N, hN⟩ := eventually_atTop.mp h
  let G : ℕ → s →ᵤ E := fun n ↦ UniformFun.ofFun (fun x ↦ F n x)
  have hc : CauchySeq (fun n ↦ G (n + N)) := by
    apply cauchySeq_of_edist_le_geometric_two 1 ENNReal.one_ne_top
    intro n
    apply UniformFun.edist_le.mpr
    intro x
    change edist (F (n + N) x) (F (n + 1 + N) x) ≤ 1 / 2 ^ n
    rw [show n + 1 + N = (n + N) + 1 by omega]
    calc
      _ ≤ (2⁻¹ : ℝ≥0∞) ^ (n + N) := hN (n + N) (Nat.le_add_left _ _) x x.property
      _ ≤ (2⁻¹ : ℝ≥0∞) ^ n := by
        rw [pow_add]
        exact mul_le_of_le_one_right'
          (show (2⁻¹ : ℝ≥0∞) ^ N ≤ 1 from pow_le_one₀ (by positivity) (by norm_num))
      _ = 1 / 2 ^ n := by simp [div_eq_mul_inv, ENNReal.inv_pow]
  obtain ⟨g, hg⟩ := cauchySeq_tendsto_of_complete hc
  have hfull : Tendsto G atTop (𝓝 g) := (tendsto_add_atTop_iff_nat N).mp hg
  have hu := UniformFun.tendsto_iff_tendstoUniformly.mp hfull
  apply Metric.uniformCauchySeqOn_iff.mpr
  intro ε hε
  obtain ⟨K, hK⟩ := Metric.uniformCauchySeqOn_iff.mp
    hu.tendstoUniformlyOn.uniformCauchySeqOn ε hε
  exact ⟨K, fun m hm n hn x hx ↦ hK m hm n hn ⟨x, hx⟩ (Set.mem_univ _)⟩
