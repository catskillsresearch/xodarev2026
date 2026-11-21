/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import Mathlib.Topology.MetricSpace.Pseudo.Real
public import Mathlib.Topology.UniformSpace.HeineCantor
public import Mathlib.Analysis.Normed.Group.Real

/-! # Uniform diagonal moduli for continuous pair functions on compact metric sets -/

@[expose] public section

open Set

namespace StochLean

theorem exists_pair_diagonal_modulus_on_compact {E : Type*} [PseudoMetricSpace E]
    {K : Set E} (hK : IsCompact K)
    {Φ : E → E → ℝ} (hΦ : Continuous (fun p : E × E ↦ Φ p.1 p.2))
    (hdiag : ∀ a ∈ K, Φ a a = 0) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ a ∈ K, ∀ b ∈ K,
      dist a b < δ → ‖Φ a b‖ < ε := by
  obtain ⟨δ, hδ, hmod⟩ := Metric.uniformContinuousOn_iff.mp
    ((hK.prod hK).uniformContinuousOn_of_continuous hΦ.continuousOn) ε hε
  refine ⟨δ, hδ, fun a ha b hb hab ↦ ?_⟩
  have hp : dist (a, a) (a, b) < δ := by
    simpa only [Prod.dist_eq, dist_self, max_eq_right dist_nonneg] using hab
  simpa only [hdiag a ha, dist_zero_left] using
    hmod (a, a) ⟨ha, ha⟩ (a, b) ⟨ha, hb⟩ hp

end StochLean
