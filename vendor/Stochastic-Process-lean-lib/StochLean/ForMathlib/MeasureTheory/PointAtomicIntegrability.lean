/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.ForMathlib.MeasureTheory.PointAtomicIntegral
public import Mathlib.MeasureTheory.Integral.Lebesgue.Countable

/-! # Integrability from actual summable point-atomic weights

The finite measure may live on an uncountable space. Only its intrinsic
countable atom set is used. The inverse singleton mass converts supported
unweighted series into integrals, with zero-mass points handled explicitly.
-/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal

namespace StochLean

variable {T : Type*} [MeasurableSpace T] [MeasurableSingletonClass T]
  {μ : Measure T} [IsFiniteMeasure μ] {f g : T → ℝ}

theorem integrable_pointAtomicPart_of_summable
    (hf : Measurable f) (hs : Summable (fun t ↦ μ.real {t} * ‖f t‖)) :
    Integrable f (pointAtomicPart μ) := by
  refine ⟨hf.aestronglyMeasurable, ?_⟩
  rw [HasFiniteIntegral, pointAtomicPart, lintegral_countable _ (countable_pointAtomSet μ)]
  have he (t : pointAtomSet μ) : ‖f t‖ₑ * μ {(t : T)} =
      ENNReal.ofReal (μ.real {(t : T)} * ‖f t‖) := by
    rw [← ofReal_norm, ← ENNReal.ofReal_toReal (measure_ne_top μ {(t : T)}),
      ← ENNReal.ofReal_mul (norm_nonneg _)]
    congr 1
    exact mul_comm _ _
  simp only [he]
  exact (hs.subtype (pointAtomSet μ)).tsum_ofReal_lt_top

theorem integrable_pointAtomicPart_div_singleton
    (hg : Measurable g) (hm : Measurable (fun t ↦ μ.real {t}))
    (hs : Summable (fun t ↦ |g t|)) :
    Integrable (fun t ↦ g t / μ.real {t}) (pointAtomicPart μ) := by
  apply integrable_pointAtomicPart_of_summable (hg.div hm)
  apply hs.of_norm_bounded
  intro t
  simp only [Pi.div_apply]
  have hm0 : 0 ≤ μ.real {t} := ENNReal.toReal_nonneg
  by_cases hz : μ.real {t} = 0
  · simp [hz, abs_nonneg]
  · rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hm0, Real.norm_eq_abs,
      abs_abs, abs_div, abs_of_nonneg hm0]
    exact (mul_div_cancel₀ |g t| hz).le

theorem integral_pointAtomicPart_div_singleton_eq_tsum
    (hg : Measurable g) (hm : Measurable (fun t ↦ μ.real {t}))
    (hs : Summable (fun t ↦ |g t|)) (hzero : ∀ t, μ {t} = 0 → g t = 0) :
    (∫ t, g t / μ.real {t} ∂pointAtomicPart μ) = ∑' t, g t := by
  rw [integral_pointAtomicPart_eq_tsum (integrable_pointAtomicPart_div_singleton hg hm hs)]
  apply tsum_congr
  intro t
  by_cases hz : μ {t} = 0
  · simp [measureReal_def, hz, hzero t hz]
  · have hn : μ.real {t} ≠ 0 :=
      ENNReal.toReal_ne_zero.mpr ⟨hz, measure_ne_top μ {t}⟩
    field_simp

end StochLean
