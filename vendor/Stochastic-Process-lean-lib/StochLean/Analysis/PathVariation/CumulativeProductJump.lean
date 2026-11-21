/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Analysis.PathVariation.CumulativeProduct

/-! # The actual left limit and jump of a cumulative product

Removing the endpoint factor is justified by absolute product convergence.
The statements allow zero factors; division by the left product is never used.
-/

@[expose] public section

open Set Filter Function
open scoped NNReal Topology

namespace StochLean

theorem multipliable_restrict_of_summable_abs_sub_one {f : ℝ≥0 → ℝ} {S : Set ℝ≥0}
    (hs : Summable (fun s : S ↦ |f s - 1|)) : Multipliable (fun s : S ↦ f s) := by
  apply (Real.multipliable_one_add_of_summable hs.of_abs).congr
  intro s
  ring

theorem leftLim_tprod_Ioc {f : ℝ≥0 → ℝ}
    (hs : ∀ T : ℝ≥0, Summable (fun s : Ioc 0 T ↦ |f s - 1|))
    {t : ℝ≥0} (ht : 0 < t) :
    leftLim (fun u : ℝ≥0 ↦ ∏' s : Ioc 0 u, f s) t = ∏' s : Ioo 0 t, f s := by
  let : (𝓝[<] t).NeBot := nhdsLT_neBot_of_exists_lt ⟨0, ht⟩
  exact leftLim_eq_of_tendsto (tendsto_tprod_Ioc_left hs t)

theorem tprod_Ioc_eq_endpoint_mul_tprod_Ioo {f : ℝ≥0 → ℝ} {t : ℝ≥0}
    (hs : Summable (fun s : Ioc 0 t ↦ |f s - 1|)) (ht : 0 < t) :
    (∏' s : Ioc 0 t, f s) = f t * ∏' s : Ioo 0 t, f s := by
  have hsub : Ioo (0 : ℝ≥0) t ⊆ Ioc 0 t := fun _ hs ↦ ⟨hs.1, hs.2.le⟩
  have hsmall : Summable (fun s : Ioo 0 t ↦ |f s - 1|) :=
    hs.comp_injective (i := Set.inclusion hsub) (Set.inclusion_injective hsub)
  have hm := multipliable_restrict_of_summable_abs_sub_one (f := f) hsmall
  have hd : Disjoint ({t} : Set ℝ≥0) (Ioo 0 t) := by simp
  have hmone : Multipliable (fun s : ({t} : Set ℝ≥0) ↦ f s) := Multipliable.of_finite
  have he : Ioc (0 : ℝ≥0) t = ({t} : Set ℝ≥0) ∪ Ioo 0 t := by
    rw [← Set.insert_eq, Ioo_insert_right ht]
  rw [he, Multipliable.tprod_union_disjoint (f := f) hd hmone hm]
  simp only [tprod_singleton]

theorem tprod_Ioc_sub_leftLim {f : ℝ≥0 → ℝ}
    (hs : ∀ T : ℝ≥0, Summable (fun s : Ioc 0 T ↦ |f s - 1|))
    {t : ℝ≥0} (ht : 0 < t) :
    (∏' s : Ioc 0 t, f s) - leftLim (fun u : ℝ≥0 ↦ ∏' s : Ioc 0 u, f s) t =
      leftLim (fun u : ℝ≥0 ↦ ∏' s : Ioc 0 u, f s) t * (f t - 1) := by
  rw [leftLim_tprod_Ioc hs ht, tprod_Ioc_eq_endpoint_mul_tprod_Ioo (hs t) ht]
  ring

end StochLean
