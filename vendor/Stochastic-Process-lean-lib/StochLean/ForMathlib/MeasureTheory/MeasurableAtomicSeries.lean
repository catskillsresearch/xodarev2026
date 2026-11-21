/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.ForMathlib.MeasureTheory.MeasurablePointAtomicPart
public import StochLean.ForMathlib.MeasureTheory.PointAtomicIntegrability

/-! # Measurability of unweighted series on sample-dependent atom sets

Dividing by the actual singleton mass represents the series as a kernel
integral. Absolute summability proves integrability, and the support
condition handles points of zero mass. Neither the time space nor a
common deterministic set containing all random atoms needs to be countable.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Function
open scoped NNReal

namespace StochLean

theorem measurable_tsum_of_support_in_kernel_atoms
    {Ω : Type*} [MeasurableSpace Ω] (κ : Kernel Ω ℝ≥0)
    (hκ : ∀ ω, IsFiniteMeasure (κ ω)) {g : Ω → ℝ≥0 → ℝ}
    (hg : Measurable (uncurry g)) (hs : ∀ ω, Summable (fun t ↦ |g ω t|))
    (hzero : ∀ ω t, κ ω {t} = 0 → g ω t = 0) :
    Measurable fun ω ↦ ∑' t, g ω t := by
  have hm : Measurable fun p : Ω × ℝ≥0 ↦ (κ p.1).real {p.2} :=
    ENNReal.measurable_toReal.comp (measurable_kernel_singleton_of_finite_fibers κ hκ)
  have hdiv : Measurable (uncurry (fun ω t ↦ g ω t / (κ ω).real {t})) := hg.div hm
  have he (ω : Ω) : (∫ t, g ω t / (κ ω).real {t} ∂pointAtomicPart (κ ω)) =
      ∑' t, g ω t := by
    let : IsFiniteMeasure (κ ω) := hκ ω
    exact integral_pointAtomicPart_div_singleton_eq_tsum
      (hg.comp measurable_prodMk_left) (hm.comp measurable_prodMk_left) (hs ω) (hzero ω)
  simpa only [he] using measurable_pointAtomicIntegral_of_finite_fibers κ hκ hdiv

end StochLean
