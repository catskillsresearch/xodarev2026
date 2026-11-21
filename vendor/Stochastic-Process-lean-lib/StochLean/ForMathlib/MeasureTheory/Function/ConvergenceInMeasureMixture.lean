/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
public import Mathlib.MeasureTheory.Integral.Lebesgue.DominatedConvergence
public import Mathlib.MeasureTheory.Integral.Lebesgue.Countable

/-! # Convergence in measure for finite-mass countable mixtures

The countable sum formula for measures holds even on nonmeasurable sets. Consequently
these results do not need a separate measurability hypothesis on the deviation sets.
-/

@[expose] public section

open Filter Set
open scoped Topology ENNReal NNReal

namespace MeasureTheory

variable {Ω E : Type*} {mΩ : MeasurableSpace Ω} [EDist E]
  {P : Measure Ω} {f : ℕ → Ω → E} {g : Ω → E}

theorem TendstoInMeasure.smul_measure (h : TendstoInMeasure P f atTop g) (c : ℝ≥0) :
    TendstoInMeasure ((c : ℝ≥0∞) • P) f atTop g := by
  intro ε hε
  simpa only [Measure.smul_apply, smul_eq_mul, mul_zero] using
    ENNReal.Tendsto.const_mul (h ε hε) (Or.inr (ENNReal.coe_ne_top : (c : ℝ≥0∞) ≠ ∞))

/-- Componentwise convergence implies convergence for a countable sum of finite total mass.
No uniformity of the componentwise rates and no measurability of `f` or `g` is assumed. -/
theorem tendstoInMeasure_sum {μ : ℕ → Measure Ω}
    (hfinite : (∑' k, μ k univ) ≠ ∞) (h : ∀ k, TendstoInMeasure (μ k) f atTop g) :
    TendstoInMeasure (Measure.sum μ) f atTop g := by
  intro ε hε
  have hlim := tendsto_lintegral_of_dominated_convergence
    (μ := Measure.count) (fun k ↦ μ k univ)
    (F := fun n k ↦ μ k {ω | ε ≤ edist (f n ω) (g ω)}) (f := fun _ ↦ 0)
    (fun _ ↦ measurable_of_countable _)
    (fun _ ↦ ae_of_all _ fun _ ↦ measure_mono (subset_univ _))
    (by simpa only [lintegral_count] using hfinite)
    (ae_of_all _ fun k ↦ h k ε hε)
  simpa only [lintegral_count, tsum_zero, Measure.sum_apply_of_countable] using hlim

end MeasureTheory
