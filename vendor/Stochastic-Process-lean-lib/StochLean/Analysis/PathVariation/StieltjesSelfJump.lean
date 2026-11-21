/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Analysis.PathVariation.StieltjesJumpSquareLimit
public import StochLean.Analysis.PathVariation.UniformPartition

/-! # The self-integral identity for a cadlag FV path

Finite-cell algebra and genuine left/right endpoint convergence prove the
identity, including the full contribution of jumps and the initial square.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal Topology

namespace StochLean

theorem square_sub_twice_leftIntegral_eq_jumpIntegral {x : ℝ≥0 → ℝ}
    (hv : LocallyBoundedVariationOn x univ) (hc : IsCadlagPath x) (T : ℝ≥0) :
    x T ^ 2 - 2 * pathStieltjesIncrementIntegral x hv hc.1 (Function.leftLim x) 0 T =
      x 0 ^ 2 + pathStieltjesIncrementIntegral x hv hc.1
        (fun u ↦ x u - Function.leftLim x u) 0 T := by
  let π : ℕ → TimePartition T := fun n ↦ (LocallyFinitePartition.dyadic n).restrict T
  have hm : Tendsto (fun n ↦ ((π n).mesh : ℝ)) atTop (𝓝 0) := by
    exact_mod_cast (NNReal.continuous_coe.tendsto 0).comp
      (LocallyFinitePartition.dyadic_admissible.restrict_mesh_tendsto (fun _ ↦ T))
  have hl := tendsto_stieltjesIncrementLeftSum_of_cadlag (hx := hv) (hr := hc.1) hc hm
  have hs : Tendsto (fun n ↦ quadraticVariationSum (π n) x) atTop
      (𝓝 (x T ^ 2 - x 0 ^ 2 -
        2 * pathStieltjesIncrementIntegral x hv hc.1 (Function.leftLim x) 0 T)) := by
    simpa only [quadraticVariationSum_eq_square_sub_leftSum] using
      (tendsto_const_nhds (x := x T ^ 2 - x 0 ^ 2)).sub (hl.const_mul 2)
  have he := tendsto_nhds_unique hs
    (tendsto_quadraticVariationSum_of_cadlag_finiteVariation hv hc hm)
  linarith

end StochLean
