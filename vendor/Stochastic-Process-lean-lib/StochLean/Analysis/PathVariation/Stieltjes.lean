/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import Mathlib.Topology.EMetricSpace.VariationOnFromTo
public import Mathlib.Topology.Order.LeftRight
public import Mathlib.MeasureTheory.Measure.Stieltjes

/-! # Stieltjes components of a right-continuous locally BV path

Only Mathlib variation and Stieltjes measures are used. The components start at
zero and represent increments after time zero. The initial value is retained
separately in the reconstruction identity; it is not inserted into an unsigned
measure when it may be negative. Local BV is not mistaken for global finite mass.
-/

@[expose] public section

open Set Filter MeasureTheory
open scoped NNReal ENNReal Topology

namespace StochLean

/-- Signed variation from the initial endpoint; on nonnegative time this is nonnegative. -/
noncomputable def pathTotalVariation (x : ℝ≥0 → ℝ) : ℝ≥0 → ℝ :=
  variationOnFromTo x univ 0

theorem pathTotalVariation_eq (x : ℝ≥0 → ℝ) (t : ℝ≥0) :
    pathTotalVariation x t = (eVariationOn x (Icc 0 t)).toReal := by
  change variationOnFromTo x univ 0 t = _
  rw [variationOnFromTo.eq_of_le x univ (show (0 : ℝ≥0) ≤ t from bot_le), univ_inter]

@[simp] theorem pathTotalVariation_zero (x : ℝ≥0 → ℝ) : pathTotalVariation x 0 = 0 :=
  variationOnFromTo.self x univ 0

theorem pathTotalVariation_nonneg (x : ℝ≥0 → ℝ) (t : ℝ≥0) :
    0 ≤ pathTotalVariation x t := variationOnFromTo.nonneg_of_le x univ bot_le

theorem pathTotalVariation_monotone {x : ℝ≥0 → ℝ}
    (hx : LocallyBoundedVariationOn x univ) : Monotone (pathTotalVariation x) :=
  fun _ _ hst ↦ variationOnFromTo.monotoneOn hx (mem_univ 0) (mem_univ _) (mem_univ _) hst

theorem rightContinuous_pathTotalVariation {x : ℝ≥0 → ℝ}
    (hx : LocallyBoundedVariationOn x univ)
    (hr : ∀ t, ContinuousWithinAt x (Ici t) t) (t : ℝ≥0) :
    ContinuousWithinAt (pathTotalVariation x) (Ici t) t := by
  apply continuousWithinAt_Ioi_iff_Ici.mp
  change Tendsto (variationOnFromTo x univ 0) (𝓝[>] t) (𝓝 (variationOnFromTo x univ 0 t))
  have h := variationOnFromTo.tendsto_right (l := x t) (mem_univ 0) (mem_univ t) hx
  simp only [univ_inter] at h
  simpa only [dist_self, add_zero] using h ((hr t).mono Ioi_subset_Ici_self)

noncomputable def pathPositiveVariation (x : ℝ≥0 → ℝ) (t : ℝ≥0) : ℝ :=
  (pathTotalVariation x t + x t - x 0) / 2

noncomputable def pathNegativeVariation (x : ℝ≥0 → ℝ) (t : ℝ≥0) : ℝ :=
  (pathTotalVariation x t - x t + x 0) / 2

@[simp] theorem pathPositiveVariation_zero (x : ℝ≥0 → ℝ) : pathPositiveVariation x 0 = 0 := by
  simp [pathPositiveVariation]

@[simp] theorem pathNegativeVariation_zero (x : ℝ≥0 → ℝ) : pathNegativeVariation x 0 = 0 := by
  simp [pathNegativeVariation]

theorem pathPositiveVariation_sub_negative (x : ℝ≥0 → ℝ) (t : ℝ≥0) :
    pathPositiveVariation x t - pathNegativeVariation x t = x t - x 0 := by
  simp only [pathPositiveVariation, pathNegativeVariation]
  ring

theorem pathPositiveVariation_add_negative (x : ℝ≥0 → ℝ) (t : ℝ≥0) :
    pathPositiveVariation x t + pathNegativeVariation x t = pathTotalVariation x t := by
  simp only [pathPositiveVariation, pathNegativeVariation]
  ring

theorem pathPositiveVariation_monotone {x : ℝ≥0 → ℝ}
    (hx : LocallyBoundedVariationOn x univ) : Monotone (pathPositiveVariation x) := by
  intro s t hst
  have h := variationOnFromTo.add_self_monotoneOn hx (mem_univ 0)
    (mem_univ s) (mem_univ t) hst
  change pathTotalVariation x s + x s ≤ pathTotalVariation x t + x t at h
  dsimp only [pathPositiveVariation]
  linarith

theorem pathNegativeVariation_monotone {x : ℝ≥0 → ℝ}
    (hx : LocallyBoundedVariationOn x univ) : Monotone (pathNegativeVariation x) := by
  intro s t hst
  have h := variationOnFromTo.sub_self_monotoneOn hx (mem_univ 0)
    (mem_univ s) (mem_univ t) hst
  change pathTotalVariation x s - x s ≤ pathTotalVariation x t - x t at h
  dsimp only [pathNegativeVariation]
  linarith

noncomputable def totalVariationStieltjes (x : ℝ≥0 → ℝ)
    (hx : LocallyBoundedVariationOn x univ) (hr : ∀ t, ContinuousWithinAt x (Ici t) t) :
    StieltjesFunction ℝ≥0 where
  toFun := pathTotalVariation x
  mono' := pathTotalVariation_monotone hx
  right_continuous' := rightContinuous_pathTotalVariation hx hr

noncomputable def positiveVariationStieltjes (x : ℝ≥0 → ℝ)
    (hx : LocallyBoundedVariationOn x univ) (hr : ∀ t, ContinuousWithinAt x (Ici t) t) :
    StieltjesFunction ℝ≥0 where
  toFun := pathPositiveVariation x
  mono' := pathPositiveVariation_monotone hx
  right_continuous' := fun t ↦ by
    have hv := rightContinuous_pathTotalVariation hx hr t
    exact ((hv.add (hr t)).sub_const (x 0)).div_const 2

noncomputable def negativeVariationStieltjes (x : ℝ≥0 → ℝ)
    (hx : LocallyBoundedVariationOn x univ) (hr : ∀ t, ContinuousWithinAt x (Ici t) t) :
    StieltjesFunction ℝ≥0 where
  toFun := pathNegativeVariation x
  mono' := pathNegativeVariation_monotone hx
  right_continuous' := fun t ↦ by
    have hv := rightContinuous_pathTotalVariation hx hr t
    exact ((hv.sub (hr t)).add_const (x 0)).div_const 2

theorem totalVariationStieltjes_eq_add (x : ℝ≥0 → ℝ)
    (hx : LocallyBoundedVariationOn x univ) (hr : ∀ t, ContinuousWithinAt x (Ici t) t) :
    totalVariationStieltjes x hx hr =
      positiveVariationStieltjes x hx hr + negativeVariationStieltjes x hx hr := by
  apply StieltjesFunction.ext
  intro t
  exact (pathPositiveVariation_add_negative x t).symm

theorem totalVariationStieltjes_measure_eq_add (x : ℝ≥0 → ℝ)
    (hx : LocallyBoundedVariationOn x univ) (hr : ∀ t, ContinuousWithinAt x (Ici t) t) :
    (totalVariationStieltjes x hx hr).measure =
      (positiveVariationStieltjes x hx hr).measure +
        (negativeVariationStieltjes x hx hr).measure := by
  rw [totalVariationStieltjes_eq_add, StieltjesFunction.measure_add]

/-- The variation measure has exactly the increment variation on each `(s,t]`. -/
theorem totalVariationStieltjes_measure_Ioc (x : ℝ≥0 → ℝ)
    (hx : LocallyBoundedVariationOn x univ) (hr : ∀ t, ContinuousWithinAt x (Ici t) t)
    {s t : ℝ≥0} (hst : s ≤ t) :
    (totalVariationStieltjes x hx hr).measure (Ioc s t) = eVariationOn x (Icc s t) := by
  rw [StieltjesFunction.measure_Ioc]
  change ENNReal.ofReal (variationOnFromTo x univ 0 t - variationOnFromTo x univ 0 s) = _
  rw [variationOnFromTo.sub_right hx (mem_univ 0) (mem_univ t) (mem_univ s),
    variationOnFromTo.eq_of_le x univ hst, univ_inter]
  apply ENNReal.ofReal_toReal
  simpa only [BoundedVariationOn, univ_inter] using hx s t (mem_univ s) (mem_univ t)

/-- Positive and negative component measures recover the original increment. -/
theorem variationStieltjes_measure_Ioc_sub (x : ℝ≥0 → ℝ)
    (hx : LocallyBoundedVariationOn x univ) (hr : ∀ t, ContinuousWithinAt x (Ici t) t)
    {s t : ℝ≥0} (hst : s ≤ t) :
    ((positiveVariationStieltjes x hx hr).measure (Ioc s t)).toReal -
      ((negativeVariationStieltjes x hx hr).measure (Ioc s t)).toReal = x t - x s := by
  rw [StieltjesFunction.measure_Ioc, StieltjesFunction.measure_Ioc,
    ENNReal.toReal_ofReal (sub_nonneg.mpr ((positiveVariationStieltjes x hx hr).mono hst)),
    ENNReal.toReal_ofReal (sub_nonneg.mpr ((negativeVariationStieltjes x hx hr).mono hst))]
  change (pathPositiveVariation x t - pathPositiveVariation x s) -
    (pathNegativeVariation x t - pathNegativeVariation x s) = _
  linarith [pathPositiveVariation_sub_negative x t, pathPositiveVariation_sub_negative x s]

/-- These are increment measures: the source initial value is a separate term. -/
theorem variationStieltjes_measure_zero (f : StieltjesFunction ℝ≥0) : f.measure {0} = 0 := by
  rw [StieltjesFunction.measure_singleton, leftLim_eq_of_isBot (show IsBot (0 : ℝ≥0) from
    fun _ ↦ bot_le), sub_self, ENNReal.ofReal_zero]

theorem totalVariationStieltjes_measure_Icc_zero (x : ℝ≥0 → ℝ)
    (hx : LocallyBoundedVariationOn x univ) (hr : ∀ t, ContinuousWithinAt x (Ici t) t)
    (T : ℝ≥0) :
    (totalVariationStieltjes x hx hr).measure (Icc 0 T) = eVariationOn x (Icc 0 T) := by
  rw [StieltjesFunction.measure_Icc,
    leftLim_eq_of_isBot (show IsBot (0 : ℝ≥0) from fun _ ↦ bot_le)]
  change ENNReal.ofReal (pathTotalVariation x T - pathTotalVariation x 0) = _
  rw [pathTotalVariation_zero, sub_zero, pathTotalVariation_eq]
  apply ENNReal.ofReal_toReal
  simpa only [BoundedVariationOn, univ_inter] using hx 0 T (mem_univ 0) (mem_univ T)

end StochLean
