/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.Path.RightContinuousSupremum
public import Mathlib.MeasureTheory.Integral.Indicator

/-! # Vanishing centered running suprema on shrinking initial windows

Right continuity at zero controls every time in each sufficiently small
initial window. The existing countable running supremum therefore tends
to zero along any sequence of shrinking horizons, without monotonicity of
the horizons. The original random initial value is subtracted, not assumed
to vanish or satisfy a moment condition.

On the single full-measure event of right-continuous paths, every strict
positive-threshold exceedance eventually disappears. Native convergence
of measurable event indicators then gives convergence of the actual
extended event measures for any finite measure. No stationarity,
independence, left limits, real-valued infinity fallback, or new supremum
construction is used.
-/

@[expose] public section

open Filter MeasureTheory Set
open scoped ENNReal NNReal Topology

namespace ProbabilityTheory

variable {Ω : Type*} {X : ℝ≥0 → Ω → ℝ}

private theorem eventually_denseRunningSupremum_norm_sub_initial_le
    {ω : Ω} (hX : IsRightContinuousPath (X · ω))
    {ι : Type*} {l : Filter ι} {δ : ι → ℝ≥0}
    (hδ : Tendsto δ l (𝓝 0)) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ i in l, denseRunningSupremum
      (fun u ω ↦ ‖X u ω - X 0 ω‖) (δ i) ω ≤ ENNReal.ofReal ε := by
  obtain ⟨r, hr, hmod⟩ := Metric.continuousWithinAt_iff.mp (hX 0) ε hε
  filter_upwards [Metric.tendsto_nhds.mp hδ r hr] with i hi
  apply denseRunningSupremum_le_of_le
  intro u hu
  have hd : dist u 0 ≤ dist (δ i) 0 := by
    simpa only [NNReal.dist_eq, NNReal.coe_zero, sub_zero,
      abs_of_nonneg u.coe_nonneg, abs_of_nonneg (δ i).coe_nonneg] using
      (show (u : ℝ) ≤ (δ i : ℝ) from hu)
  have hb := hmod (show u ∈ Ici (0 : ℝ≥0) from by simp) (hd.trans_lt hi)
  simpa only [dist_eq_norm] using hb.le

/-- The actual centered countable running supremum of a right-continuous
path tends to zero on shrinking initial windows, along an arbitrary filter. -/
theorem IsRightContinuousPath.tendsto_denseRunningSupremum_norm_sub_initial
    {ω : Ω} (hX : IsRightContinuousPath (X · ω))
    {ι : Type*} {l : Filter ι} {δ : ι → ℝ≥0}
    (hδ : Tendsto δ l (𝓝 0)) :
    Tendsto (fun i ↦ denseRunningSupremum
      (fun u ω ↦ ‖X u ω - X 0 ω‖) (δ i) ω) l (𝓝 0) := by
  apply ENNReal.tendsto_nhds_zero.mpr
  intro ε hε
  by_cases htop : ε = ∞
  · subst ε
    exact Eventually.of_forall fun _ ↦ le_top
  have hpos : 0 < ε.toReal := ENNReal.toReal_pos hε.ne' htop
  filter_upwards [eventually_denseRunningSupremum_norm_sub_initial_le hX hδ hpos]
    with i hi
  simpa only [ENNReal.ofReal_toReal htop] using hi

/-- Under a finite measure, the probability of a strict positive-level
exceedance on a shrinking initial window tends to zero. Coordinates are
measurable, paths are right-continuous on one common almost-sure event,
and neither initial moments nor monotone shrinking horizons are required. -/
theorem HasRightContinuousPaths.tendsto_measure_denseRunningSupremum_norm_sub_initial
    {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsFiniteMeasure P]
    (hr : HasRightContinuousPaths X P) (hm : ∀ t, Measurable (X t))
    {δ : ℕ → ℝ≥0} (hδ : Tendsto δ atTop (𝓝 0)) {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun n ↦ P {ω | ENNReal.ofReal ε < denseRunningSupremum
      (fun u ω ↦ ‖X u ω - X 0 ω‖) (δ n) ω}) atTop (𝓝 0) := by
  let E : ℕ → Set Ω := fun n ↦ {ω | ENNReal.ofReal ε < denseRunningSupremum
    (fun u ω ↦ ‖X u ω - X 0 ω‖) (δ n) ω}
  have hmE (n : ℕ) : MeasurableSet (E n) :=
    measurableSet_denseRunningSupremum_gt (fun u ↦ ((hm u).sub (hm 0)).norm) (δ n) ε
  have hlim : ∀ᵐ ω ∂P, ∀ᶠ n in atTop, ω ∈ E n ↔ ω ∈ (∅ : Set Ω) := by
    filter_upwards [hr] with ω hω
    have hsmall := (hω.tendsto_denseRunningSupremum_norm_sub_initial hδ).eventually
      (Iio_mem_nhds (ENNReal.ofReal_pos.mpr hε))
    filter_upwards [hsmall] with n hn
    exact iff_of_false (not_lt_of_ge hn.le) (notMem_empty ω)
  simpa only [measure_empty] using
    tendsto_measure_of_ae_tendsto_indicator_of_isFiniteMeasure
      (μ := P) (As := E) atTop (A := ∅) MeasurableSet.empty hmE hlim

end ProbabilityTheory
