/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import Mathlib.MeasureTheory.Measure.Stieltjes
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun
public import Mathlib.Analysis.Calculus.Deriv.Slope

/-! # An absolutely continuous Stieltjes function has an absolutely continuous measure

Absolute continuity of the original function on a compact interval implies
absolute continuity of its actual Stieltjes measure restricted to the
corresponding open-closed interval. The proof identifies that restricted
measure with Lebesgue measure weighted by the actual nonnegative derivative.

The derivative is genuinely integrable on every relevant subinterval by
Mathlib's absolute-continuity theorem. The fundamental theorem of calculus
then identifies all interval masses, and measure extensionality supplies
the measure equality. No density representation, absolute continuity of
the measure, or differentiability certificate is assumed in addition to
the original function's absolute continuity. Reversed or degenerate
integration intervals are handled by the actual empty-set convention.
-/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal

namespace StieltjesFunction

/-- The actual Stieltjes measure of a function that is absolutely continuous
on a compact interval is absolutely continuous with respect to Lebesgue
measure after restriction to the corresponding open-closed interval. -/
theorem restrict_absolutelyContinuous_of_absolutelyContinuousOnInterval
    (F : StieltjesFunction ℝ) {a b : ℝ}
    (hF : AbsolutelyContinuousOnInterval F a b) :
    F.measure.restrict (Ioc a b) ≪ volume := by
  by_cases hab : a ≤ b
  · have heq : F.measure.restrict (Ioc a b) =
        (volume.withDensity (fun x : ℝ ↦ ENNReal.ofReal (deriv F x))).restrict
          (Ioc a b) := by
      refine Measure.ext_of_Ioc' _ _ ?_ ?_
      · intro c d _
        exact ne_top_of_le_ne_top (measure_Ioc_lt_top (μ := F.measure)).ne
          (Measure.restrict_apply_le _ _)
      · intro c d _
        rw [Measure.restrict_apply measurableSet_Ioc,
          Measure.restrict_apply measurableSet_Ioc]
        have hinter : Ioc c d ∩ Ioc a b = Ioc (max c a) (min d b) := by
          ext x
          simp only [mem_inter_iff, mem_Ioc, max_lt_iff, le_min_iff]
          exact ⟨fun h ↦ ⟨⟨h.1.1, h.2.1⟩, h.1.2, h.2.2⟩,
            fun h ↦ ⟨⟨h.1.1, h.2.1⟩, h.1.2, h.2.2⟩⟩
        rw [hinter]
        by_cases hcd : max c a < min d b
        · have hsub : uIcc (max c a) (min d b) ⊆ uIcc a b := by
            rw [uIcc_of_le hcd.le, uIcc_of_le hab]
            intro x hx
            exact ⟨(le_max_right c a).trans hx.1,
              hx.2.trans (min_le_right d b)⟩
          have hAC := hF.mono hsub
          have hi : IntegrableOn (deriv F) (Ioc (max c a) (min d b)) volume :=
            (intervalIntegrable_iff_integrableOn_Ioc_of_le hcd.le).mp
              hAC.intervalIntegrable_deriv
          have hn : 0 ≤ᵐ[volume.restrict (Ioc (max c a) (min d b))] deriv F :=
            ae_of_all _ fun _ ↦ F.mono.deriv_nonneg
          rw [F.measure_Ioc, withDensity_apply _ measurableSet_Ioc,
            ← ofReal_integral_eq_lintegral_ofReal hi hn,
            ← intervalIntegral.integral_of_le hcd.le, hAC.integral_deriv_eq_sub]
        · rw [Ioc_eq_empty hcd, measure_empty, measure_empty]
    rw [heq]
    exact Measure.absolutelyContinuous_restrict.trans
      (withDensity_absolutelyContinuous volume _)
  · rw [Ioc_eq_empty (not_lt.mpr (le_of_not_ge hab)), Measure.restrict_empty]
    exact Measure.AbsolutelyContinuous.zero volume

end StieltjesFunction
