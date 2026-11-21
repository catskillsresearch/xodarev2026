/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Analysis.PathVariation.StieltjesIntegral
public import StochLean.Analysis.PathVariation.TerminalVariation

/-! # Quantitative variation of the actual Stieltjes integral

Bounded measurable integrands multiply the integrator's extended variation
by at most their bound, on compact intervals and on the whole half-line.
The existing path integral and Mathlib variation remain the only owners.

The source initial term `f 0 * x 0` cancels in every increment; it is not a
variation-measure atom. Only compact variations are converted to real numbers,
after local BV supplies their finiteness. The global estimate stays in
`ENNReal`, including infinite variation and the case of a zero multiplier.
-/

@[expose] public section

open Set Filter MeasureTheory Finset
open scoped NNReal ENNReal Topology

namespace StochLean

variable {x : ℝ≥0 → ℝ} {hx : LocallyBoundedVariationOn x univ}
  {hr : ∀ t, ContinuousWithinAt x (Ici t) t} {f : ℝ≥0 → ℝ}

/-- The integral's initial term cancels, and the upper endpoint of the
remaining increment is included, even when the integrator jumps there. -/
theorem pathStieltjesIntegral_sub_eq_incrementIntegral {s t : ℝ≥0}
    (hf : IntegrableOn f (Ioc 0 t) (totalVariationStieltjes x hx hr).measure)
    (hst : s ≤ t) :
    pathStieltjesIntegral x hx hr f t - pathStieltjesIntegral x hx hr f s =
      pathStieltjesIncrementIntegral x hx hr f s t := by
  have hs : Ioc 0 s ⊆ Ioc 0 t := fun _ hu ↦ ⟨hu.1, hu.2.trans hst⟩
  have he : Ioc 0 t \ Ioc 0 s = Ioc s t := by
    ext u
    constructor
    · rintro ⟨⟨hu0, hut⟩, hus⟩
      exact ⟨lt_of_not_ge (fun h ↦ hus ⟨hu0, h⟩), hut⟩
    · rintro ⟨hus, hut⟩
      exact ⟨⟨lt_of_le_of_lt bot_le hus, hut⟩, fun h ↦ (not_le.mpr hus) h.2⟩
  have hp := setIntegral_sdiff measurableSet_Ioc (integrableOn_positiveVariationStieltjes hf) hs
  have hn := setIntegral_sdiff measurableSet_Ioc (integrableOn_negativeVariationStieltjes hf) hs
  rw [he] at hp hn
  simp only [pathStieltjesIntegral, pathStieltjesIncrementIntegral]
  rw [hp, hn]
  ring

private theorem pathTotalVariation_sub_eq (hx : LocallyBoundedVariationOn x univ)
    (s t : ℝ≥0) (hst : s ≤ t) :
    pathTotalVariation x t - pathTotalVariation x s = (eVariationOn x (Icc s t)).toReal := by
  change variationOnFromTo x univ 0 t - variationOnFromTo x univ 0 s = _
  rw [variationOnFromTo.sub_right hx (mem_univ 0) (mem_univ t) (mem_univ s),
    variationOnFromTo.eq_of_le x univ hst, univ_inter]

/-- A measurable integrand bounded on `(0,T]` controls the variation of the
actual primitive on `[0,T]`. No bound on the separate initial term is needed. -/
theorem eVariationOn_pathStieltjesIntegral_Icc_le (T : ℝ≥0)
    (hf : Measurable f) {C : ℝ} (hC : 0 ≤ C)
    (hb : ∀ u ∈ Ioc 0 T, ‖f u‖ ≤ C) :
    eVariationOn (pathStieltjesIntegral x hx hr f) (Icc 0 T) ≤
      ENNReal.ofReal C * eVariationOn x (Icc 0 T) := by
  have hi : IntegrableOn f (Ioc 0 T) (totalVariationStieltjes x hx hr).measure :=
    integrableOn_variationStieltjes_of_bounded hf hb
  have hinc (s t : ℝ≥0) (hst : s ≤ t) (ht : t ≤ T) :
      ‖pathStieltjesIntegral x hx hr f t - pathStieltjesIntegral x hx hr f s‖ ≤
        C * (pathTotalVariation x t - pathTotalVariation x s) := by
    rw [pathStieltjesIntegral_sub_eq_incrementIntegral
      (hi.mono_set (fun _ hu ↦ ⟨hu.1, hu.2.trans ht⟩)) hst,
      pathTotalVariation_sub_eq hx s t hst]
    exact norm_pathStieltjesIncrementIntegral_le
      (fun u hu ↦ hb u ⟨lt_of_le_of_lt bot_le hu.1, hu.2.trans ht⟩) hst
  apply iSup_le
  rintro ⟨n, ⟨u, hu, hus⟩⟩
  have hsum : (∑ i ∈ range n,
      ‖pathStieltjesIntegral x hx hr f (u (i + 1)) -
        pathStieltjesIntegral x hx hr f (u i)‖) ≤
      C * pathTotalVariation x T := by
    calc
      _ ≤ ∑ i ∈ range n,
          C * (pathTotalVariation x (u (i + 1)) - pathTotalVariation x (u i)) :=
        sum_le_sum fun i _ ↦ hinc _ _ (hu (Nat.le_succ i)) (hus (i + 1)).2
      _ = C * (pathTotalVariation x (u n) - pathTotalVariation x (u 0)) := by
        rw [← mul_sum, sum_range_sub (fun i ↦ pathTotalVariation x (u i)) n]
      _ ≤ C * pathTotalVariation x T :=
        mul_le_mul_of_nonneg_left
          ((sub_le_self _ (pathTotalVariation_nonneg x _)).trans
            (pathTotalVariation_monotone hx (hus n).2)) hC
  calc
    _ = ENNReal.ofReal (∑ i ∈ range n,
        ‖pathStieltjesIntegral x hx hr f (u (i + 1)) -
          pathStieltjesIntegral x hx hr f (u i)‖) := by
      simp only [edist_dist, dist_eq_norm]
      rw [ENNReal.ofReal_sum_of_nonneg (fun i _ ↦ norm_nonneg _)]
    _ ≤ ENNReal.ofReal (C * pathTotalVariation x T) := ENNReal.ofReal_le_ofReal hsum
    _ = _ := by
      have hxT : BoundedVariationOn x (Icc 0 T) := by
        simpa only [univ_inter] using hx 0 T (mem_univ 0) (mem_univ T)
      rw [ENNReal.ofReal_mul hC, pathTotalVariation_eq,
        ENNReal.ofReal_toReal hxT]

/-- The full-half-line estimate retains infinite variation. In particular
it does not convert an infinite global variation into the real number zero. -/
theorem eVariationOn_pathStieltjesIntegral_univ_le
    (hf : Measurable f) {C : ℝ} (hC : 0 ≤ C)
    (hb : ∀ u, 0 < u → ‖f u‖ ≤ C) :
    eVariationOn (pathStieltjesIntegral x hx hr f) univ ≤
      ENNReal.ofReal C * eVariationOn x univ := by
  rw [eVariationOn_univ_eq_iSup_Icc_nat]
  refine iSup_le fun n ↦ (eVariationOn_pathStieltjesIntegral_Icc_le
    (x := x) (hx := hx) (hr := hr) (n : ℝ≥0) hf hC (fun u hu ↦ hb u hu.1)).trans ?_
  gcongr
  exact eVariationOn.mono x (subset_univ (Icc 0 (n : ℝ≥0)))

end StochLean
