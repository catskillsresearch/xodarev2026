/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.ForMathlib.Analysis.PairDiagonalModulus
public import StochLean.Probability.Process.Path.CadlagFiniteOscillation
public import StochLean.Analysis.PathVariation.CadlagCompositionBounds

/-! # Small diagonal pair coefficients outside finitely many cadlag crossings -/

@[expose] public section

open Set ProbabilityTheory
open scoped NNReal

namespace StochLean

theorem exists_finite_separators_pair_diagonal {E : Type*}
    [NormedAddCommGroup E] [ProperSpace E] {x : ℝ≥0 → E}
    (hx : IsCadlagPath x) (T : ℝ≥0) {Φ : E → E → ℝ}
    (hΦ : Continuous (fun p : E × E ↦ Φ p.1 p.2)) (hdiag : ∀ a, Φ a a = 0)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ A : Finset ℝ≥0, (∀ s ∈ A, s ∈ Ioc 0 T) ∧ ∃ δ : ℝ, 0 < δ ∧
      ∀ a ∈ Icc 0 T, ∀ b ∈ Icc 0 T, a ≤ b → dist a b < δ →
        (∀ s ∈ A, s ∉ Ioc a b) → ‖Φ (x a) (x b)‖ < ε := by
  classical
  obtain ⟨R, _, hR⟩ := hx.exists_norm_bound_Icc T
  have hxK (s : ℝ≥0) (hs : s ∈ Icc 0 T) : x s ∈ Metric.closedBall 0 R := by
    have h := hR s hs
    simpa only [Metric.mem_closedBall, dist_zero_right] using h
  obtain ⟨η, hη, hmod⟩ := exists_pair_diagonal_modulus_on_compact
    (isCompact_closedBall (0 : E) R) hΦ (fun a _ ↦ hdiag a) hε
  obtain ⟨A, hA, δ, hδ, hosc⟩ := hx.exists_finite_separators_oscillation T hη
  refine ⟨A.filter (fun s ↦ 0 < s), ?_, δ, hδ, ?_⟩
  · intro s hs
    have hs' := Finset.mem_filter.mp hs
    exact ⟨hs'.2, (hA hs'.1).2⟩
  · intro a ha b hb hab hd havoid
    apply hmod (x a) (hxK a ha) (x b) (hxK b hb)
    apply hosc a ha b hb hab hd
    intro s hs hsc
    exact havoid s (Finset.mem_filter.mpr ⟨hs, ha.1.trans_lt hsc.1⟩) hsc

end StochLean
