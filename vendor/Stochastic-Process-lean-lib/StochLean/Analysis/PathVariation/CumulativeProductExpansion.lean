/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Analysis.PathVariation.CumulativeProduct
public import Mathlib.Data.Finset.Lattice.Fold

/-! # Expanding a cumulative product into an actual step series

A finite-subset coefficient is the product of its factor deviations and
is activated at the greatest time in that subset. The empty subset has
coefficient one and activation time zero. The coefficient series is
absolutely convergent, including for products with zero or negative factors.
-/

@[expose] public section

open Set
open scoped NNReal

namespace StochLean

theorem summable_abs_cumulativeProduct_coefficients {f : ℝ≥0 → ℝ} {T : ℝ≥0}
    (hs : Summable (fun s : Ioc 0 T ↦ |f s - 1|)) :
    Summable (fun S : Finset (Ioc 0 T) ↦ |∏ s ∈ S, (f s - 1)|) :=
  (summable_finsetProd_of_summable_norm hs.of_abs.norm).abs

theorem tprod_Ioc_eq_tsum_finset_stepCutoff {f : ℝ≥0 → ℝ} {T : ℝ≥0}
    (hs : Summable (fun s : Ioc 0 T ↦ |f s - 1|)) (t : ℝ≥0) :
    (∏' s : Ioc 0 (min T t), f s) =
      ∑' S : Finset (Ioc 0 T),
        if S.sup (fun s ↦ (s : ℝ≥0)) ≤ t then ∏ s ∈ S, (f s - 1) else 0 := by
  classical
  have hg : Summable (fun s : Ioc 0 T ↦ ‖if (s : ℝ≥0) ≤ t then f s - 1 else 0‖) :=
    (hs.of_abs.indicator {s | (s : ℝ≥0) ≤ t}).norm
  calc
    _ = ∏' s : Ioc 0 T, (1 + if (s : ℝ≥0) ≤ t then f s - 1 else 0) := by
      rw [← tprod_Ioc_cutoff_le f t T]
      apply tprod_congr
      intro s
      split_ifs <;> ring
    _ = ∑' S : Finset (Ioc 0 T),
        ∏ s ∈ S, (if (s : ℝ≥0) ≤ t then f s - 1 else 0) :=
      tprod_one_add (summable_finsetProd_of_summable_norm hg)
    _ = _ := by
      apply tsum_congr
      intro S
      simp only [Finset.prod_ite_zero, Finset.sup_le_iff]

end StochLean
