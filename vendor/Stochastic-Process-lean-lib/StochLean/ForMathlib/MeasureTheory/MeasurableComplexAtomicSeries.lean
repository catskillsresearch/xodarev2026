/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.ForMathlib.MeasureTheory.MeasurableAtomicSeries
public import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic

/-! # Complex series on sample-dependent atom sets

The real and imaginary series use the same finite-fiber kernel and its
intrinsic atoms. Actual complex summability justifies coordinate sums.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Function
open scoped NNReal

namespace StochLean

theorem measurable_complex_tsum_of_support_in_kernel_atoms
    {Ω : Type*} [MeasurableSpace Ω] (κ : Kernel Ω ℝ≥0)
    (hκ : ∀ ω, IsFiniteMeasure (κ ω)) {g : Ω → ℝ≥0 → ℂ}
    (hg : Measurable (uncurry g)) (hs : ∀ ω, Summable (g ω))
    (hzero : ∀ ω t, κ ω {t} = 0 → g ω t = 0) :
    Measurable fun ω ↦ ∑' t, g ω t := by
  have hr := measurable_tsum_of_support_in_kernel_atoms κ hκ
    (g := fun ω t ↦ (g ω t).re)
    (Complex.measurable_re.comp hg)
    (fun ω ↦ (Complex.hasSum_re (hs ω).hasSum).summable.abs)
    (fun ω t ht ↦ congrArg Complex.re (hzero ω t ht))
  have hi := measurable_tsum_of_support_in_kernel_atoms κ hκ
    (g := fun ω t ↦ (g ω t).im)
    (Complex.measurable_im.comp hg)
    (fun ω ↦ (Complex.hasSum_im (hs ω).hasSum).summable.abs)
    (fun ω t ht ↦ congrArg Complex.im (hzero ω t ht))
  have h := (Complex.measurable_ofReal.comp hr).add
    ((Complex.measurable_ofReal.comp hi).mul_const Complex.I)
  change Measurable (fun ω ↦ Complex.ofReal (∑' t, (g ω t).re) +
    Complex.ofReal (∑' t, (g ω t).im) * Complex.I) at h
  have hre (ω : Ω) := Complex.re_tsum (hs ω)
  have him (ω : Ω) := Complex.im_tsum (hs ω)
  simpa only [← hre, ← him, Complex.re_add_im] using h

end StochLean
