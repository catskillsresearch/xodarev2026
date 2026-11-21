/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Analysis.PathVariation.CumulativeStepSeries
public import StochLean.ForMathlib.RestrictedFiberSum

/-! # An absolutely summable step series is exactly its initial value plus its jumps

Repeated activation times are grouped by their actual fibers. The sum of
positive-time jumps excludes coefficients already present at time zero.
-/

@[expose] public section

open Set Function
open scoped NNReal

namespace StochLean

theorem tsum_stepCutoff_sub_initial_eq_tsum_jumps {ι : Type*} {w : ι → ℝ}
    (a : ι → ℝ≥0) (hw : Summable (fun i ↦ |w i|)) (t : ℝ≥0) :
    (∑' i, if a i ≤ t then w i else 0) - (∑' i, if a i ≤ 0 then w i else 0) =
      ∑' s : Ioc 0 t, ((∑' i, if a i ≤ s then w i else 0) -
        leftLim (fun u ↦ ∑' i, if a i ≤ u then w i else 0) s) := by
  classical
  have hj (s : Ioc 0 t) := tsum_stepCutoff_sub_leftLim a hw s.2.1
  simp only [hj]
  rw [tsum_subtype_fiberwise hw.of_abs a (Ioc 0 t)]
  have hc : Summable (fun i ↦ if a i ≤ t then w i else 0) :=
    hw.of_abs.indicator {i | a i ≤ t}
  have hz : Summable (fun i ↦ if a i ≤ 0 then w i else 0) :=
    hw.of_abs.indicator {i | a i ≤ 0}
  rw [← hc.tsum_sub hz]
  apply tsum_congr
  intro i
  by_cases hi0 : a i = 0
  · simp [Set.indicator, hi0]
  · have hp : 0 < a i := pos_iff_ne_zero.mpr hi0
    by_cases hit : a i ≤ t <;> simp [Set.indicator, hp, hit, not_le.mpr hp]

end StochLean
