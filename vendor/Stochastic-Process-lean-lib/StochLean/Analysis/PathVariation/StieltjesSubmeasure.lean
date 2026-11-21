/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.ForMathlib.MeasurableStieltjesNNReal
public import Mathlib.MeasureTheory.Measure.Real

/-! # A genuine Stieltjes realization of a submeasure

A measure dominated by a half-line Stieltjes measure is finite on every initial
interval and has no mass at zero. Its cumulative mass is right-continuous by
the original path's right continuity and the domination of interval increments.
-/

@[expose] public section

open MeasureTheory Set Filter
open scoped NNReal ENNReal Topology

namespace StochLean

variable (f : StieltjesFunction ℝ≥0) {ν : Measure ℝ≥0} (hν : ν ≤ f.measure)

include hν

theorem stieltjesSubmeasure_Iic_lt_top (t : ℝ≥0) : ν (Iic t) < ∞ := by
  apply lt_of_le_of_lt ((Measure.le_iff'.mp hν) _)
  rw [stieltjesMeasure_Iic_nnreal]
  exact ENNReal.ofReal_lt_top

theorem stieltjesSubmeasure_Iic_zero : ν (Iic 0) = 0 := by
  have h := (Measure.le_iff'.mp hν) (Iic 0)
  simpa only [stieltjesMeasure_Iic_nnreal, sub_self, ENNReal.ofReal_zero,
    nonpos_iff_eq_zero] using h

theorem stieltjesSubmeasure_real_increment {s t : ℝ≥0} (hst : s ≤ t) :
    ν.real (Iic t) - ν.real (Iic s) = ν.real (Ioc s t) := by
  rw [← Iic_sdiff_Iic]
  exact (measureReal_sdiff (Iic_subset_Iic.mpr hst) measurableSet_Iic
    (stieltjesSubmeasure_Iic_lt_top f hν t).ne).symm

theorem stieltjesSubmeasure_real_increment_le {s t : ℝ≥0} (hst : s ≤ t) :
    ν.real (Iic t) - ν.real (Iic s) ≤ f t - f s := by
  rw [stieltjesSubmeasure_real_increment f hν hst]
  have h := ENNReal.toReal_mono
    (show f.measure (Ioc s t) ≠ ∞ from measure_Ioc_lt_top.ne)
    ((Measure.le_iff'.mp hν) (Ioc s t))
  simpa only [measureReal_def, StieltjesFunction.measure_Ioc,
    ENNReal.toReal_ofReal (sub_nonneg.mpr (f.mono hst))] using h

theorem monotone_stieltjesSubmeasure_cumulative : Monotone (fun t ↦ ν.real (Iic t)) := by
  intro s t hst
  exact measureReal_mono (Iic_subset_Iic.mpr hst) (stieltjesSubmeasure_Iic_lt_top f hν t).ne

theorem rightContinuous_stieltjesSubmeasure_cumulative (s : ℝ≥0) :
    ContinuousWithinAt (fun t ↦ ν.real (Iic t)) (Ici s) s := by
  have hu : Tendsto (fun t ↦ ν.real (Iic s) + (f t - f s)) (𝓝[≥] s)
      (𝓝 (ν.real (Iic s))) := by
    simpa only [sub_self, add_zero] using
      tendsto_const_nhds.add ((f.right_continuous s).sub_const (f s))
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hu
  · filter_upwards [self_mem_nhdsWithin] with t ht
    exact monotone_stieltjesSubmeasure_cumulative f hν ht
  · filter_upwards [self_mem_nhdsWithin] with t ht
    linarith [stieltjesSubmeasure_real_increment_le f hν ht]

noncomputable def stieltjesSubmeasure : StieltjesFunction ℝ≥0 where
  toFun t := ν.real (Iic t)
  mono' := monotone_stieltjesSubmeasure_cumulative f hν
  right_continuous' := rightContinuous_stieltjesSubmeasure_cumulative f hν

@[simp] theorem stieltjesSubmeasure_zero : stieltjesSubmeasure f hν 0 = 0 := by
  change (ν (Iic 0)).toReal = 0
  rw [stieltjesSubmeasure_Iic_zero f hν, ENNReal.toReal_zero]

theorem stieltjesSubmeasure_measure_Iic (t : ℝ≥0) :
    (stieltjesSubmeasure f hν).measure (Iic t) = ν (Iic t) := by
  rw [stieltjesMeasure_Iic_nnreal, stieltjesSubmeasure_zero, sub_zero]
  exact ofReal_measureReal (stieltjesSubmeasure_Iic_lt_top f hν t).ne

theorem stieltjesSubmeasure_measure : (stieltjesSubmeasure f hν).measure = ν := by
  have hu : (⋃ n : ℕ, Iic (n : ℝ≥0)) = univ := by
    ext t
    simp only [mem_iUnion, mem_Iic, mem_univ, iff_true]
    exact ⟨Nat.ceil t, Nat.le_ceil t⟩
  apply Measure.ext_of_iUnion_eq_univ hu
  intro n
  let μ := (stieltjesSubmeasure f hν).measure
  have : IsFiniteMeasure (μ.restrict (Iic (n : ℝ≥0))) :=
    ⟨by rw [Measure.restrict_apply_univ, stieltjesSubmeasure_measure_Iic]
        exact stieltjesSubmeasure_Iic_lt_top f hν n⟩
  apply Measure.ext_of_Iic
  intro t
  simp only [Measure.restrict_apply measurableSet_Iic, Iic_inter_Iic,
    stieltjesSubmeasure_measure_Iic]

end StochLean
