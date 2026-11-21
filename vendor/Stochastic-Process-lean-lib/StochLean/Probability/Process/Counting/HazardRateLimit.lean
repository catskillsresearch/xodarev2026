/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Slope
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.MeasureTheory.Measure.Real
public import Mathlib.MeasureTheory.Measure.WithDensity

/-! # The actual conditional small-window hazard rate

A genuine probability density, continuous at the queried time, gives the
right small-window conditional probability rate as density divided by
survival. The numerator is the original law of `[t, t + h)`, and the
conditioning event is the original closed survival event `[t, infinity)`.
Its probability is explicitly positive; a totalized zero denominator is
not interpreted as a conditional probability.

The density is proved integrable from its actual finite total mass. The
window mass is then its genuine Bochner integral, and the native fundamental
theorem of calculus supplies the right difference-quotient limit. Neither
a CDF derivative nor a desired window limit is assumed as a certificate.

This is only the hazard-rate limit in the example on Protter's printed
pages 123-124. It does not implement the subsequent censored-data example,
introduce a separate hazard-rate selector, or require a positive lifetime
when the rate formula itself is valid at an arbitrary real time.
-/

@[expose] public section

open MeasureTheory Filter Set
open scoped ENNReal Topology

namespace ProbabilityTheory

/-- The original conditional probability of an arrival in a short right
window, divided by its width, tends to density over positive survival. -/
theorem tendsto_conditional_window_rate_of_density
    {μ : Measure ℝ} [IsProbabilityMeasure μ] {f : ℝ → ℝ} {t : ℝ}
    (hf : Measurable f) (hn : 0 ≤ᵐ[volume] f)
    (hμ : μ = volume.withDensity (fun x ↦ ENNReal.ofReal (f x)))
    (hct : ContinuousAt f t) (hs : 0 < μ (Ici t)) :
    Tendsto (fun h : ℝ ↦ (μ.real (Ico t (t + h)) / μ.real (Ici t)) / h)
      (𝓝[>] 0) (𝓝 (f t / μ.real (Ici t))) := by
  have hmass : (∫⁻ x, ENNReal.ofReal (f x)) = μ univ := by
    rw [hμ, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
  have hfi : Integrable f volume := by
    apply (lintegral_ofReal_ne_top_iff_integrable hf.aestronglyMeasurable hn).mp
    rw [hmass]
    exact measure_ne_top μ univ
  have hwindow (h : ℝ) (hh : 0 < h) :
      μ.real (Ico t (t + h)) = ∫ x in t..t + h, f x := by
    calc
      μ.real (Ico t (t + h)) = ∫ x in Ico t (t + h), f x := by
        rw [measureReal_def, hμ, withDensity_apply _ measurableSet_Ico]
        exact (integral_eq_lintegral_of_nonneg_ae (ae_restrict_of_ae hn)
          hfi.integrableOn.aestronglyMeasurable).symm
      _ = ∫ x in Ioc t (t + h), f x := integral_Ico_eq_integral_Ioc
      _ = ∫ x in t..t + h, f x :=
        (intervalIntegral.integral_of_le (le_add_of_nonneg_right hh.le)).symm
  have hderiv : HasDerivAt (fun u : ℝ ↦ ∫ x in t..u, f x) (f t) t :=
    intervalIntegral.integral_hasDerivAt_right hfi.intervalIntegrable
      hf.stronglyMeasurable.stronglyMeasurableAtFilter hct
  have havg : Tendsto (fun h : ℝ ↦ (∫ x in t..t + h, f x) / h)
      (𝓝[>] 0) (𝓝 (f t)) := by
    simpa only [smul_eq_mul, intervalIntegral.integral_same, sub_zero,
      div_eq_mul_inv, mul_comm] using hderiv.tendsto_slope_zero_right
  have hlimit : Tendsto (fun h : ℝ ↦ μ.real (Ico t (t + h)) / h)
      (𝓝[>] 0) (𝓝 (f t)) := by
    apply havg.congr'
    filter_upwards [self_mem_nhdsWithin] with h hh
    rw [hwindow h hh]
  have hsurvival : 0 < μ.real (Ici t) :=
    ENNReal.toReal_pos hs.ne' (measure_ne_top μ (Ici t))
  apply (hlimit.div tendsto_const_nhds hsurvival.ne').congr'
  refine Eventually.of_forall fun h ↦ ?_
  change (μ.real (Ico t (t + h)) / h) / μ.real (Ici t) =
    (μ.real (Ico t (t + h)) / μ.real (Ici t)) / h
  ring

end ProbabilityTheory
