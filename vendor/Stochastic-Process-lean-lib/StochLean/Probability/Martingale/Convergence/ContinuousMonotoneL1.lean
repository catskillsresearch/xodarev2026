/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Martingale.Convergence.MonotoneL1
public import StochLean.Probability.Process.Filtration.Reindex
public import StochLean.Probability.Process.ClassD.Basic
public import StochLean.Probability.Martingale.OptionalSampling.ContinuousUsual
public import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-! # Actual terminal limits of increasing processes on the whole half-line

The existing discrete monotone convergence theorem supplies the terminal
variable from integer observations. Monotonicity upgrades this same limit
to all nonnegative real times and gives a common-event integrable envelope.
There is no second terminal selector, supremum definition, or assumed terminal
bound. No path regularity is needed for this construction or its L1 limit.

Right continuity and the usual conditions are used only by the Class D
consumer, to obtain measurability of arbitrary finite stopping values.
-/

@[expose] public section

open MeasureTheory Filter
open scoped NNReal ENNReal Topology

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsFiniteMeasure P]
  {F : Filtration ℝ≥0 mΩ} {A : ℝ≥0 → Ω → ℝ} {C : ℝ}

/-- A uniform first-moment bound constructs an actual integrable terminal
variable for a nonnegative increasing process. The limit, common envelope,
UI, and L1 convergence hold over the entire half-line, not only the integers. -/
theorem HasMonotonePaths.exists_integrable_terminal_of_integral_bounded
    (hm : HasMonotonePaths A P) (ha : Adapted F A)
    (hi : ∀ t, Integrable (A t) P) (hn : ∀ᵐ ω ∂P, ∀ t, 0 ≤ A t ω)
    (hb : ∀ t, (∫ ω, A t ω ∂P) ≤ C) :
    ∃ Z : Ω → ℝ, Integrable Z P ∧ (∫ ω, Z ω ∂P) ≤ C ∧
      (∀ᵐ ω ∂P, ∀ t, 0 ≤ A t ω ∧ A t ω ≤ Z ω) ∧
      (∀ᵐ ω ∂P, Tendsto (fun t : ℝ≥0 ↦ A t ω) atTop (𝓝 (Z ω))) ∧
      UniformIntegrable A 1 P ∧
      Tendsto (fun t : ℝ≥0 ↦ eLpNorm (A t - Z) 1 P) atTop (𝓝 0) := by
  let e : ℕ → ℝ≥0 := Nat.cast
  have he : Monotone e := fun _ _ h ↦ Nat.cast_le.mpr h
  let G := F.reindex e he
  have hmn : HasMonotonePaths (fun n ↦ A (e n)) P :=
    hm.mono fun _ hω ↦ hω.comp he
  have han : Adapted G (fun n ↦ A (e n)) := fun n ↦ ha (e n)
  obtain ⟨Z, hiZ, hlZ, _, hL1n⟩ :=
    hmn.exists_integrable_limit_of_nonneg_of_integral_bounded han
      (fun n ↦ hi (e n)) (fun n ↦ hn.mono fun _ hω ↦ hω (e n)) (fun n ↦ hb (e n))
  have hgrid : Tendsto e atTop atTop := tendsto_natCast_atTop_atTop
  have hlim : ∀ᵐ ω ∂P, Tendsto (fun t : ℝ≥0 ↦ A t ω) atTop (𝓝 (Z ω)) := by
    filter_upwards [hm, hlZ] with ω hmω hω
    exact (tendsto_iff_tendsto_subseq_of_monotone hmω hgrid).mpr hω.2
  have hall : ∀ᵐ ω ∂P, ∀ t, 0 ≤ A t ω ∧ A t ω ≤ Z ω := by
    filter_upwards [hm, hn, hlim] with ω hmω hnω hlω t
    exact ⟨hnω t, hmω.ge_of_tendsto hlω t⟩
  have hEZ : (∫ ω, Z ω ∂P) ≤ C :=
    le_of_tendsto (tendsto_integral_of_L1' Z hiZ.aestronglyMeasurable
      (Eventually.of_forall fun n ↦ hi (e n)) hL1n)
      (Eventually.of_forall fun n ↦ hb (e n))
  have hui : UniformIntegrable A 1 P := by
    apply (uniformIntegrable_const le_rfl ENNReal.one_ne_top
      (memLp_one_iff_integrable.mpr hiZ)).mono_norm
      (fun t ↦ (hi t).aestronglyMeasurable)
    intro t
    filter_upwards [hall] with ω hω
    rw [Real.norm_of_nonneg (hω t).1, Real.norm_of_nonneg ((hω t).1.trans (hω t).2)]
    exact (hω t).2
  have hnorm : Tendsto (fun t : ℝ≥0 ↦ ∫ ω, ‖A t ω - Z ω‖ ∂P) atTop (𝓝 0) := by
    have hmeas : ∀ᶠ t : ℝ≥0 in atTop,
        AEStronglyMeasurable (fun ω ↦ ‖A t ω - Z ω‖) P :=
      Eventually.of_forall fun t ↦ ((hi t).sub hiZ).aestronglyMeasurable.norm
    have hbound : ∀ᶠ t : ℝ≥0 in atTop, ∀ᵐ ω ∂P, ‖‖A t ω - Z ω‖‖ ≤ Z ω := by
      apply Eventually.of_forall
      intro t
      filter_upwards [hall] with ω hω
      rw [norm_norm, Real.norm_eq_abs, abs_of_nonpos (sub_nonpos.mpr (hω t).2)]
      linarith [(hω t).1]
    have hl : ∀ᵐ ω ∂P,
        Tendsto (fun t : ℝ≥0 ↦ ‖A t ω - Z ω‖) atTop (𝓝 (0 : ℝ)) := by
      filter_upwards [hlim] with ω hω
      have hconst : Tendsto (fun _ : ℝ≥0 ↦ Z ω) atTop (𝓝 (Z ω)) := tendsto_const_nhds
      simpa only [sub_self, norm_zero] using (hω.sub hconst).norm
    simpa only [integral_zero] using
      tendsto_integral_filter_of_dominated_convergence Z hmeas hbound hiZ hl
  refine ⟨Z, hiZ, hEZ, hall, hlim, hui, ?_⟩
  have heNorm (t : ℝ≥0) : eLpNorm (A t - Z) 1 P =
      ENNReal.ofReal (∫ ω, ‖A t ω - Z ω‖ ∂P) := by
    rw [eLpNorm_one_eq_lintegral_enorm]
    exact (ofReal_integral_norm_eq_lintegral_enorm ((hi t).sub hiZ)).symm
  simp_rw [heNorm]
  simpa only [Function.comp_def, ENNReal.ofReal_zero] using
    (ENNReal.continuous_ofReal.tendsto (0 : ℝ)).comp hnorm

/-- Right-continuous increasing processes with uniformly bounded first
moments are Class D. The terminal envelope is constructed by the preceding
theorem and bounds every stopping value on one common full-measure event. -/
theorem HasMonotonePaths.isClassD_of_nonneg_of_integral_bounded
    (hm : HasMonotonePaths A P) (ha : Adapted F A)
    (hi : ∀ t, Integrable (A t) P) (hn : ∀ᵐ ω ∂P, ∀ t, 0 ≤ A t ω)
    (hb : ∀ t, (∫ ω, A t ω ∂P) ≤ C) (hF : F.IsUsual P)
    (hr : HasRightContinuousPaths A P) : IsClassD A F P := by
  obtain ⟨Z, hiZ, _, hall, _, _, _⟩ :=
    hm.exists_integrable_terminal_of_integral_bounded ha hi hn hb
  apply (uniformIntegrable_const le_rfl ENNReal.one_ne_top
    (memLp_one_iff_integrable.mpr hiZ)).mono_norm
  · intro τ
    have hmeas := ha.stronglyAdapted.measurable_stoppedValue_of_usual hF hr τ.isStoppingTime
    exact (hmeas.mono τ.measurableSpace_le le_rfl).aestronglyMeasurable
  · intro τ
    filter_upwards [hall] with ω hω
    rw [Real.norm_of_nonneg (hω (τ ω)).1,
      Real.norm_of_nonneg ((hω (τ ω)).1.trans (hω (τ ω)).2)]
    exact (hω (τ ω)).2

end ProbabilityTheory
