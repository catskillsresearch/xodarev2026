/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Analysis.PathVariation.CumulativeProduct
public import StochLean.ForMathlib.MonotoneIndicatorVariation

/-! # Local finite variation of absolutely convergent cumulative products

Expanding the product over finite subsets expresses it as an absolutely
convergent sum. Every subset coefficient is activated at most once as
time increases. This proves finite variation without taking logarithms,
excluding zero factors, or assuming positivity.
-/

@[expose] public section

open Set
open scoped NNReal

namespace StochLean

theorem locallyBoundedVariationOn_tprod_monotone_cutoff
    {α ι : Type*} [LinearOrder α] {a : α → Set ι} (ha : Monotone a)
    {w : ι → ℝ} (hw : Summable (fun i ↦ |w i|)) :
    LocallyBoundedVariationOn
      (fun t ↦ ∏' i, (a t).mulIndicator (fun i ↦ 1 + w i) i) univ := by
  classical
  let W : Finset ι → ℝ := fun s ↦ ∏ i ∈ s, w i
  let A : α → Set (Finset ι) := fun t ↦ {s | ∀ i ∈ s, i ∈ a t}
  have hA : Monotone A := fun _ _ hst _ hs i hi ↦ ha hst (hs i hi)
  have hW : Summable (fun s ↦ |W s|) :=
    (summable_finsetProd_of_summable_norm hw.of_abs.norm).abs
  have hv := locallyBoundedVariationOn_tsum_monotone_indicator (w := W) hA hW
  have he (t : α) : (∏' i, (a t).mulIndicator (fun i ↦ 1 + w i) i) =
      ∑' s, (A t).indicator W s := by
    have hg : Summable (fun i ↦ ‖(a t).indicator w i‖) :=
      (hw.of_abs.indicator (a t)).norm
    convert tprod_one_add (summable_finsetProd_of_summable_norm hg) using 1
    · apply tprod_congr
      intro i
      by_cases hi : i ∈ a t <;> simp [Set.mulIndicator, Set.indicator, hi]
    · apply tsum_congr
      intro s
      simp only [Set.indicator, Finset.prod_ite_zero, A, mem_ofPred_eq, W]
  simpa only [← he] using hv

theorem locallyBoundedVariationOn_tprod_Ioc {f : ℝ≥0 → ℝ}
    (hs : ∀ T : ℝ≥0, Summable (fun s : Ioc 0 T ↦ |f s - 1|)) :
    LocallyBoundedVariationOn (fun t : ℝ≥0 ↦ ∏' s : Ioc 0 t, f s) univ := by
  classical
  intro a b ha hb
  let A : ℝ≥0 → Set (Ioc (0 : ℝ≥0) b) := fun t ↦ {s | (s : ℝ≥0) ≤ t}
  have hA : Monotone A := fun _ _ htu _ hs ↦ hs.trans htu
  have hv := locallyBoundedVariationOn_tprod_monotone_cutoff
    (w := fun s : Ioc 0 b ↦ f s - 1) hA (hs b)
  have he (t : ℝ≥0) :
      (∏' s : Ioc 0 b, (A t).mulIndicator (fun s ↦ 1 + (f s - 1)) s) =
        ∏' s : Ioc 0 (min b t), f s := by
    convert tprod_Ioc_cutoff_le f t b using 1
    apply tprod_congr
    intro s
    simp only [Set.mulIndicator, A, mem_ofPred_eq, add_sub_cancel]
  have hvab := hv a b ha hb
  change eVariationOn _ _ ≠ ⊤ at hvab ⊢
  rw [eVariationOn.eq_of_eqOn (f' := fun t : ℝ≥0 ↦ ∏' s : Ioc 0 t, f s) (by
    intro t ht
    change (∏' s : Ioc 0 b, (A t).mulIndicator (fun s ↦ 1 + (f s - 1)) s) = _
    rw [he, min_eq_right ht.2.2])] at hvab
  exact hvab

end StochLean
