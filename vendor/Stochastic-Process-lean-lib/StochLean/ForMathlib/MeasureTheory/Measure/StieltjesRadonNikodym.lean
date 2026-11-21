/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.ForMathlib.MeasureTheory.StieltjesOrder
public import Mathlib.MeasureTheory.Measure.Decomposition.IntegralRNDeriv

/-! # Radon--Nikodym densities between ordered Stieltjes measures

This is the deterministic measure-theoretic part of Protter I.52.  If the
increments of `A` are bounded by the increments of `C`, then the Stieltjes
measure of `A` is dominated by that of `C`.  Its native Radon--Nikodym
derivative is therefore a measurable density with values in `[0, 1]` almost
everywhere, and it recovers every Stieltjes increment.

The source theorem uses a particular *one-sided rational liminf* version of
this density.  Identifying that version with `stieltjesRNDensity` requires the
one-sided differentiation theorem for an arbitrary locally finite reference
measure; that identification is intentionally not claimed here.
-/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal NNReal

namespace StochLean

/-- The native extended-valued Radon--Nikodym density of the Stieltjes measure
of `A` with respect to the Stieltjes measure of `C`. -/
noncomputable def stieltjesRNDensityENNReal (A C : StieltjesFunction ℝ≥0) : ℝ≥0 → ℝ≥0∞ :=
  A.measure.rnDeriv C.measure

/-- The real-valued Radon--Nikodym density used by pathwise Stieltjes
integration. -/
noncomputable def stieltjesRNDensity (A C : StieltjesFunction ℝ≥0) : ℝ≥0 → ℝ :=
  fun t ↦ (stieltjesRNDensityENNReal A C t).toReal

theorem measurable_stieltjesRNDensityENNReal (A C : StieltjesFunction ℝ≥0) :
    Measurable (stieltjesRNDensityENNReal A C) :=
  Measure.measurable_rnDeriv _ _

theorem measurable_stieltjesRNDensity (A C : StieltjesFunction ℝ≥0) :
    Measurable (stieltjesRNDensity A C) :=
  (measurable_stieltjesRNDensityENNReal A C).ennreal_toReal

theorem stieltjesRNDensity_nonneg (A C : StieltjesFunction ℝ≥0) (t : ℝ≥0) :
    0 ≤ stieltjesRNDensity A C t :=
  ENNReal.toReal_nonneg

theorem stieltjesMeasure_absolutelyContinuous_of_increment_le
    (A C : StieltjesFunction ℝ≥0)
    (hAC : ∀ s t, s ≤ t → A t - A s ≤ C t - C s) :
    A.measure ≪ C.measure :=
  (stieltjesMeasure_le_of_increment_le A C hAC).absolutelyContinuous

theorem withDensity_stieltjesRNDensityENNReal_eq
    (A C : StieltjesFunction ℝ≥0)
    (hAC : ∀ s t, s ≤ t → A t - A s ≤ C t - C s) :
    C.measure.withDensity (stieltjesRNDensityENNReal A C) = A.measure :=
  Measure.withDensity_rnDeriv_eq _ _
    (stieltjesMeasure_absolutelyContinuous_of_increment_le A C hAC)

theorem stieltjesRNDensity_ae_le_one
    (A C : StieltjesFunction ℝ≥0)
    (hAC : ∀ s t, s ≤ t → A t - A s ≤ C t - C s) :
    ∀ᵐ t ∂C.measure, stieltjesRNDensity A C t ≤ 1 := by
  have hle : A.measure ≤ C.measure := stieltjesMeasure_le_of_increment_le A C hAC
  filter_upwards [Measure.rnDeriv_le_one_of_le hle] with t ht
  have htop : stieltjesRNDensityENNReal A C t ≠ ∞ :=
    ne_top_of_le_ne_top ENNReal.one_ne_top ht
  simpa only [stieltjesRNDensity, ENNReal.toReal_one] using
    (ENNReal.toReal_le_toReal htop ENNReal.one_ne_top).2 ht

theorem integrableOn_stieltjesRNDensity_Ioc
    (A C : StieltjesFunction ℝ≥0) (s t : ℝ≥0) :
    IntegrableOn (stieltjesRNDensity A C) (Ioc s t) C.measure := by
  exact Measure.integrableOn_toReal_rnDeriv
    (ne_of_lt (show A.measure (Ioc s t) < ∞ from measure_Ioc_lt_top))

/-- The RN density recovers every increment of `A` from the Stieltjes measure
of `C`. -/
theorem integral_stieltjesRNDensity_Ioc
    (A C : StieltjesFunction ℝ≥0)
    (hAC : ∀ s t, s ≤ t → A t - A s ≤ C t - C s)
    {s t : ℝ≥0} (hst : s ≤ t) :
    ∫ u in Ioc s t, stieltjesRNDensity A C u ∂C.measure = A t - A s := by
  have hac := stieltjesMeasure_absolutelyContinuous_of_increment_le A C hAC
  calc
    ∫ u in Ioc s t, stieltjesRNDensity A C u ∂C.measure =
        A.measure.real (Ioc s t) := Measure.setIntegral_toReal_rnDeriv hac _
    _ = A t - A s := by
      rw [measureReal_def, StieltjesFunction.measure_Ioc,
        ENNReal.toReal_ofReal (sub_nonneg.mpr (A.mono hst))]

/-! ### The deterministic signed density layer -/

/-- Difference of the positive and negative RN densities with respect to a
common increasing reference function. -/
noncomputable def stieltjesSignedRNDensity
    (P N V : StieltjesFunction ℝ≥0) : ℝ≥0 → ℝ :=
  fun t ↦ stieltjesRNDensity P V t - stieltjesRNDensity N V t

theorem measurable_stieltjesSignedRNDensity
    (P N V : StieltjesFunction ℝ≥0) :
    Measurable (stieltjesSignedRNDensity P N V) :=
  (measurable_stieltjesRNDensity P V).sub (measurable_stieltjesRNDensity N V)

theorem stieltjesSignedRNDensity_ae_mem_Icc
    (P N V : StieltjesFunction ℝ≥0)
    (hPV : ∀ s t, s ≤ t → P t - P s ≤ V t - V s)
    (hNV : ∀ s t, s ≤ t → N t - N s ≤ V t - V s) :
    ∀ᵐ t ∂V.measure, stieltjesSignedRNDensity P N V t ∈ Set.Icc (-1 : ℝ) 1 := by
  filter_upwards [stieltjesRNDensity_ae_le_one P V hPV,
    stieltjesRNDensity_ae_le_one N V hNV] with t hP hN
  exact ⟨by
    dsimp only [stieltjesSignedRNDensity]
    linarith [stieltjesRNDensity_nonneg P V t, stieltjesRNDensity_nonneg N V t], by
    dsimp only [stieltjesSignedRNDensity]
    linarith [stieltjesRNDensity_nonneg P V t, stieltjesRNDensity_nonneg N V t]⟩

/-- The signed RN density recovers the difference of two increasing
Stieltjes increments. -/
theorem integral_stieltjesSignedRNDensity_Ioc
    (P N V : StieltjesFunction ℝ≥0)
    (hPV : ∀ s t, s ≤ t → P t - P s ≤ V t - V s)
    (hNV : ∀ s t, s ≤ t → N t - N s ≤ V t - V s)
    {s t : ℝ≥0} (hst : s ≤ t) :
    ∫ u in Ioc s t, stieltjesSignedRNDensity P N V u ∂V.measure =
      (P t - P s) - (N t - N s) := by
  simp only [stieltjesSignedRNDensity]
  rw [integral_sub (integrableOn_stieltjesRNDensity_Ioc P V s t)
    (integrableOn_stieltjesRNDensity_Ioc N V s t),
    integral_stieltjesRNDensity_Ioc P V hPV hst,
    integral_stieltjesRNDensity_Ioc N V hNV hst]

end StochLean
