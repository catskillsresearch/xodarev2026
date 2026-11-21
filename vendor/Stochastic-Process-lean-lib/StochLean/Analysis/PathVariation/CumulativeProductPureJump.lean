/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Analysis.PathVariation.CumulativeProductExpansion
public import StochLean.Analysis.PathVariation.CumulativeProductJump
public import StochLean.Analysis.PathVariation.CumulativeStepSeriesPureJump

/-! # A cumulative product changes exactly by the sum of its actual jumps

The finite-subset expansion is an absolutely summable step series on each
finite horizon. This proves the pure-jump identity without cancellation
of factors or division by the product. Its initial value is one.
-/

@[expose] public section

open Set Filter Function
open scoped NNReal Topology

namespace StochLean

theorem tprod_Ioc_sub_one_eq_tsum_jumps {f : ℝ≥0 → ℝ}
    (hs : ∀ T : ℝ≥0, Summable (fun s : Ioc 0 T ↦ |f s - 1|)) (t : ℝ≥0) :
    (∏' s : Ioc 0 t, f s) - 1 =
      ∑' s : Ioc 0 t, ((∏' u : Ioc 0 (s : ℝ≥0), f u) -
        leftLim (fun v : ℝ≥0 ↦ ∏' u : Ioc 0 v, f u) s) := by
  classical
  let w : Finset (Ioc (0 : ℝ≥0) t) → ℝ := fun S ↦ ∏ s ∈ S, (f s - 1)
  let a : Finset (Ioc (0 : ℝ≥0) t) → ℝ≥0 := fun S ↦ S.sup (fun s ↦ (s : ℝ≥0))
  have hw : Summable (fun S ↦ |w S|) :=
    summable_abs_cumulativeProduct_coefficients (f := f) (hs t)
  have he (v : ℝ≥0) : (∑' S, if a S ≤ v then w S else 0) =
      ∏' s : Ioc 0 (min t v), f s :=
    (tprod_Ioc_eq_tsum_finset_stepCutoff (f := f) (hs t) v).symm
  have hj := tsum_stepCutoff_sub_initial_eq_tsum_jumps a hw t
  simp only [he] at hj
  rw [min_self, min_zero] at hj
  have hz : (∏' s : Ioc (0 : ℝ≥0) 0, f s) = 1 := by simp
  rw [hz] at hj
  convert hj using 1
  apply tsum_congr
  intro s
  rw [min_eq_right s.2.2]
  congr 1
  rw [leftLim_tprod_Ioc (f := f) hs s.2.1]
  symm
  let : (𝓝[<] (s : ℝ≥0)).NeBot := nhdsLT_neBot_of_exists_lt ⟨0, s.2.1⟩
  apply leftLim_eq_of_tendsto
  apply (tendsto_tprod_Ioc_left (f := f) hs s).congr'
  filter_upwards [self_mem_nhdsWithin] with v hv
  rw [min_eq_right ((show v < s from hv).le.trans s.2.2)]

theorem tprod_Ioc_sub_one_eq_tsum_left_mul_deviation {f : ℝ≥0 → ℝ}
    (hs : ∀ T : ℝ≥0, Summable (fun s : Ioc 0 T ↦ |f s - 1|)) (t : ℝ≥0) :
    (∏' s : Ioc 0 t, f s) - 1 =
      ∑' s : Ioc 0 t,
        leftLim (fun v : ℝ≥0 ↦ ∏' u : Ioc 0 v, f u) s * (f s - 1) := by
  rw [tprod_Ioc_sub_one_eq_tsum_jumps hs t]
  apply tsum_congr
  intro s
  exact tprod_Ioc_sub_leftLim hs s.2.1

end StochLean
