/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import Mathlib.MeasureTheory.Integral.IntervalIntegral.LebesgueDifferentiationThm
public import Mathlib.MeasureTheory.Measure.Decomposition.IntegralRNDeriv

/-! # Actual right-window rates of finite absolutely continuous measures

For a finite real measure absolutely continuous with respect to Lebesgue
measure, its actual mass on `[t,t+h)`, divided by `h`, tends at almost every
time to the existing Radon-Nikodym density. No pointwise continuity of a
density, primitive derivative, or desired window limit is an assumption.

The native real RN representative is genuinely L1 by finiteness of the
measure. Lebesgue differentiation applies to its actual interval primitive.
Absolute continuity identifies each window mass with its real RN integral;
the Lebesgue-null endpoint exchange then matches the right derivative.
The conclusion is only almost everywhere in time, not a pointwise assertion
at every endpoint or about an arbitrary value of an RN representative.
-/

@[expose] public section

open Filter Set
open scoped ENNReal Topology

namespace MeasureTheory.Measure

/-- At almost every real time, a finite absolutely continuous measure's
actual right `Ico` mass per unit width tends to its native RN density. -/
theorem ae_tendsto_measureReal_Ico_div (μ : Measure ℝ) [IsFiniteMeasure μ]
    (hAC : μ ≪ volume) :
    ∀ᵐ t ∂volume, Tendsto (fun h : ℝ ↦ μ.real (Ico t (t + h)) / h)
      (𝓝[>] 0) (𝓝 ((μ.rnDeriv volume t).toReal)) := by
  let f : ℝ → ℝ := fun x ↦ (μ.rnDeriv volume x).toReal
  have hfi : Integrable f volume := Measure.integrable_toReal_rnDeriv
  filter_upwards [LocallyIntegrable.ae_hasDerivAt_integral hfi.locallyIntegrable] with t ht
  have hderiv : HasDerivAt (fun u : ℝ ↦ ∫ x in t..u, f x) (f t) t := ht t
  have havg : Tendsto (fun h : ℝ ↦ (∫ x in t..t + h, f x) / h)
      (𝓝[>] 0) (𝓝 (f t)) := by
    simpa only [smul_eq_mul, intervalIntegral.integral_same, sub_zero,
      div_eq_mul_inv, mul_comm] using hderiv.tendsto_slope_zero_right
  apply havg.congr'
  filter_upwards [self_mem_nhdsWithin] with h hh
  have hwindow : μ.real (Ico t (t + h)) = ∫ x in t..t + h, f x := by
    calc
      μ.real (Ico t (t + h)) = ∫ x in Ico t (t + h), f x :=
        (Measure.setIntegral_toReal_rnDeriv hAC (Ico t (t + h))).symm
      _ = ∫ x in Ioc t (t + h), f x := integral_Ico_eq_integral_Ioc
      _ = ∫ x in t..t + h, f x :=
        (intervalIntegral.integral_of_le (le_add_of_nonneg_right hh.le)).symm
  rw [hwindow]

end MeasureTheory.Measure
