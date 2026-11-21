/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.ForMathlib.MeasureTheory.PointAtomicDecomposition
public import StochLean.ForMathlib.MeasureTheory.CountablySupportedIntegral

/-! # Integration against the intrinsic point-atomic part

The series identity requires actual integrability. The underlying space need
not be countable: only the positive-mass singletons are counted.
-/

@[expose] public section

open MeasureTheory Set Function

namespace StochLean

variable {T : Type*} [MeasurableSpace T] [MeasurableSingletonClass T]
  {μ : Measure T} [SFinite μ] {f : T → ℝ}

theorem integral_pointAtomicPart_eq_tsum (hf : Integrable f (pointAtomicPart μ)) :
    ∫ t, f t ∂pointAtomicPart μ = ∑' t, μ.real {t} * f t := by
  calc
    _ = ∑' t : pointAtomSet μ, μ.real {(t : T)} * f t := by
      simpa only [pointAtomicPart, smul_eq_mul] using
        setIntegral_countable f (countable_pointAtomSet μ) hf
    _ = ∑' t, μ.real {t} * f t := by
      apply tsum_subtype_eq_of_support_subset
        (f := fun t : T ↦ μ.real {t} * f t) (s := pointAtomSet μ)
      intro t ht
      by_contra ha
      have hz : μ {t} = 0 := not_not.mp ha
      exact ht (by simp only [measureReal_def, hz, ENNReal.toReal_zero, zero_mul])

theorem setIntegral_pointAtomicPart_eq_tsum {s : Set T} (hs : MeasurableSet s)
    (hf : IntegrableOn f s (pointAtomicPart μ)) :
    ∫ t in s, f t ∂pointAtomicPart μ = ∑' t : s, μ.real {(t : T)} * f t := by
  classical
  calc
    _ = ∫ t, s.indicator f t ∂pointAtomicPart μ := (integral_indicator hs).symm
    _ = ∑' t, μ.real {t} * s.indicator f t :=
      integral_pointAtomicPart_eq_tsum (hf.integrable_indicator hs)
    _ = ∑' t, s.indicator (fun u ↦ μ.real {u} * f u) t := by
      apply tsum_congr
      intro t
      by_cases ht : t ∈ s
      · rw [indicator_of_mem ht, indicator_of_mem ht]
      · rw [indicator_of_notMem ht, indicator_of_notMem ht, mul_zero]
    _ = ∑' t : s, μ.real {(t : T)} * f t := (tsum_subtype s _).symm

theorem setIntegral_eq_pointDiffusePart_add_tsum {s : Set T} (hs : MeasurableSet s)
    (hf : IntegrableOn f s μ) :
    ∫ t in s, f t ∂μ = (∫ t in s, f t ∂pointDiffusePart μ) +
      ∑' t : s, μ.real {(t : T)} * f t := by
  have ha : IntegrableOn f s (pointAtomicPart μ) := hf.mono_measure (pointAtomicPart_le μ)
  have hd : IntegrableOn f s (pointDiffusePart μ) := hf.mono_measure (pointDiffusePart_le μ)
  calc
    _ = (∫ t in s, f t ∂pointAtomicPart μ) +
        ∫ t in s, f t ∂pointDiffusePart μ := by
      rw [← integral_add_measure ha hd, ← Measure.restrict_add,
        pointAtomicPart_add_pointDiffusePart]
    _ = (∫ t in s, f t ∂pointDiffusePart μ) +
        ∑' t : s, μ.real {(t : T)} * f t := by
      rw [setIntegral_pointAtomicPart_eq_tsum hs ha, add_comm]

end StochLean
