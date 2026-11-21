/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure
public import Mathlib.MeasureTheory.Integral.Bochner.Set

/-! # Integrals of countably supported functions on uncountable spaces -/

@[expose] public section

open MeasureTheory Set Function

namespace StochLean

variable {α : Type*} [MeasurableSpace α] [MeasurableSingletonClass α]
  {μ : Measure α} {f : α → ℝ}

theorem integral_eq_tsum_of_countable_support (hc : (support f).Countable)
    (hf : Integrable f μ) : ∫ t, f t ∂μ = ∑' t, μ.real {t} * f t := by
  calc
    _ = ∫ t in support f, f t ∂μ :=
      (setIntegral_eq_integral_of_forall_compl_eq_zero (fun _ ht ↦ not_not.mp ht)).symm
    _ = ∑' t : support f, μ.real {(t : α)} * f t := by
      simpa only [smul_eq_mul] using setIntegral_countable f hc hf.integrableOn
    _ = ∑' t, μ.real {t} * f t := by
      apply tsum_subtype_eq_of_support_subset (f := fun t : α ↦ μ.real {t} * f t)
        (s := support f)
      intro t ht hf0
      exact ht (by
        change μ.real {t} * f t = 0
        rw [hf0, mul_zero])

theorem setIntegral_eq_tsum_of_countable_support (hc : (support f).Countable)
    {s : Set α} (hs : MeasurableSet s) (hf : IntegrableOn f s μ) :
    ∫ t in s, f t ∂μ = ∑' t : s, μ.real {(t : α)} * f t := by
  classical
  have hc' : (support (s.indicator f)).Countable := hc.mono (by
    intro t ht hf0
    by_cases hts : t ∈ s
    · exact ht (by rw [indicator_of_mem hts, hf0])
    · exact ht (indicator_of_notMem hts f))
  calc
    _ = ∫ t, s.indicator f t ∂μ := (integral_indicator hs).symm
    _ = ∑' t, μ.real {t} * s.indicator f t :=
      integral_eq_tsum_of_countable_support hc' (hf.integrable_indicator hs)
    _ = ∑' t, s.indicator (fun u ↦ μ.real {u} * f u) t := by
      apply tsum_congr
      intro t
      by_cases ht : t ∈ s
      · rw [indicator_of_mem ht, indicator_of_mem ht]
      · rw [indicator_of_notMem ht, indicator_of_notMem ht, mul_zero]
    _ = ∑' t : s, μ.real {(t : α)} * f t := (tsum_subtype s _).symm

end StochLean
