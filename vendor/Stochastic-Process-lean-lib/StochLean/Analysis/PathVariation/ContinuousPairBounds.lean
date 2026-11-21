/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Analysis.PathVariation.EndpointPairStep
public import Mathlib.Topology.MetricSpace.Pseudo.Real
public import Mathlib.Topology.MetricSpace.Lipschitz

/-! # Uniform bounds near the diagonal of a continuous path pair -/

@[expose] public section

open Set Filter
open scoped NNReal Topology

namespace StochLean

theorem exists_pair_diagonal_modulus_of_continuous {T : ℝ≥0} {x : ℝ≥0 → ℝ}
    (hx : ContinuousOn x (Icc 0 T)) {Φ : ℝ → ℝ → ℝ}
    (hΦ : Continuous (fun p : ℝ × ℝ ↦ Φ p.1 p.2)) (hdiag : ∀ a, Φ a a = 0)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ a ∈ Icc 0 T, ∀ b ∈ Icc 0 T,
      dist a b < δ → ‖Φ (x a) (x b)‖ < ε := by
  let K : Set (ℝ≥0 × ℝ≥0) := Icc 0 T ×ˢ Icc 0 T
  have hK : IsCompact K := isCompact_Icc.prod isCompact_Icc
  have hl : ContinuousOn (fun p : ℝ≥0 × ℝ≥0 ↦ x p.1) K :=
    hx.comp continuous_fst.continuousOn (fun _ hp ↦ hp.1)
  have hr : ContinuousOn (fun p : ℝ≥0 × ℝ≥0 ↦ x p.2) K :=
    hx.comp continuous_snd.continuousOn (fun _ hp ↦ hp.2)
  have hg : ContinuousOn (fun p : ℝ≥0 × ℝ≥0 ↦ Φ (x p.1) (x p.2)) K :=
    hΦ.comp_continuousOn (hl.prodMk hr)
  obtain ⟨δ, hδ, hmod⟩ := Metric.uniformContinuousOn_iff.mp
    (hK.uniformContinuousOn_of_continuous hg) ε hε
  refine ⟨δ, hδ, fun a ha b hb hab ↦ ?_⟩
  have hp : dist (a, a) (a, b) < δ := by
    simpa only [Prod.dist_eq, dist_self, max_eq_right dist_nonneg] using hab
  simpa only [hdiag, dist_zero_left] using hmod (a, a) ⟨ha, ha⟩ (a, b) ⟨ha, hb⟩ hp

theorem TimePartition.dist_stopped_endpoints_le_mesh {S : ℝ≥0} (π : TimePartition S)
    (t : ℝ≥0) (i : Fin π.size) :
    dist (min (π.left i) t) (min (π.right i) t) ≤ (π.mesh : ℝ) := by
  calc
    _ ≤ dist (π.left i) (π.right i) := by
      have h := (LipschitzWith.id.min_const (t : ℝ)).dist_le_mul
        (π.left i : ℝ) (π.right i : ℝ)
      simpa only [NNReal.dist_eq, NNReal.coe_min, Real.dist_eq, NNReal.coe_one, one_mul,
        id_eq] using h
    _ = (π.gap i : ℝ) := by rw [dist_comm]; exact π.dist_right_left_eq_gap i
    _ ≤ π.mesh := by exact_mod_cast π.gap_le_mesh i

end StochLean
