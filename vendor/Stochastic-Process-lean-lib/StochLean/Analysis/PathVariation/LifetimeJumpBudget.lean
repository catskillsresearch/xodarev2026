/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Analysis.PathVariation.LifetimeJumpSeries

/-! # Whole-half-line budgets for actual disjoint positive jumps

Every finite set of finite lifetimes lies below a finite path-dependent
horizon. The established compact jump estimate therefore controls every
finite partial sum by the original global variation. Infinite lifetimes
carry zero, and no summability or moment of the number of jumps is assumed.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set Function
open scoped NNReal ENNReal

namespace StochLean

/-- A disjoint family of positive jumps has every finite absolute partial
sum bounded by the actual whole-half-line variation. -/
theorem sum_abs_jumps_le_global_variation_of_disjoint_finite_lifetimes
    {ι : Type*} {y : ℝ≥0 → ℝ} {g : ι → ℝ} {τ : ι → WithTop ℝ≥0}
    (hv : LocallyBoundedVariationOn y univ)
    (hr : ∀ t, ContinuousWithinAt y (Ici t) t)
    (hfin : eVariationOn y univ ≠ ∞)
    (hpos : ∀ i, 0 < τ i)
    (hdisj : ∀ i j (t : ℝ≥0),
      τ i = (t : WithTop ℝ≥0) → τ j = (t : WithTop ℝ≥0) → i = j)
    (htop : ∀ i, τ i = ⊤ → g i = 0)
    (hcoe : ∀ i (t : ℝ≥0), τ i = (t : WithTop ℝ≥0) → g i = y t - leftLim y t)
    (s : Finset ι) : (∑ i ∈ s, |g i|) ≤ (eVariationOn y univ).toReal := by
  classical
  let T : ℝ≥0 := s.sup (fun i ↦ (τ i).untopD 0)
  let G : ι → ℝ := fun i ↦ if τ i ≤ (T : WithTop ℝ≥0) then g i else 0
  have hGtop (i : ι) (hi : τ i = ⊤) : G i = 0 := by
    simp only [G, hi, WithTop.top_le_iff, WithTop.coe_ne_top, if_false]
  have hGcoe (i : ι) (t : ℝ≥0) (hi : τ i = (t : WithTop ℝ≥0)) :
      G i = (Ioc 0 T).indicator (fun u ↦ (1 : ℝ) * (y u - leftLim y u)) t := by
    have ht : 0 < t := WithTop.coe_lt_coe.mp (hi ▸ hpos i)
    by_cases hb : t ≤ T
    · simp only [G, hi, WithTop.coe_le_coe, hb, if_true,
        indicator_of_mem (show t ∈ Ioc 0 T from ⟨ht, hb⟩), one_mul, hcoe i t hi]
    · simp only [G, hi, WithTop.coe_le_coe, hb, if_false,
        indicator_of_notMem (show t ∉ Ioc 0 T from fun h ↦ hb h.2)]
  have he (i : ι) (hi : i ∈ s) : G i = g i := by
    by_cases ht : τ i = ⊤
    · rw [hGtop i ht, htop i ht]
    · let t := (τ i).untopA
      have htcoe : τ i = (t : WithTop ℝ≥0) := by
        dsimp only [t]
        rw [WithTop.untopA_eq_untop ht, WithTop.coe_untop]
      have hb : t ≤ T := by
        simpa only [htcoe, WithTop.untopD_coe] using
          (Finset.le_sup (f := fun j ↦ (τ j).untopD 0) hi)
      simp only [G, htcoe, WithTop.coe_le_coe, hb, if_true]
  have h := sum_abs_weighted_jumps_le_of_disjoint_finite_lifetimes
    hv hr hfin T (C := 1) zero_le_one (fun _ _ ↦ by simp)
    hdisj hGtop hGcoe s
  simpa only [Finset.sum_congr rfl (fun i hi ↦ congrArg abs (he i hi)), one_mul] using h

end StochLean
