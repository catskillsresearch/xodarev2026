/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.TimeChange.ClockInverse
public import StochLean.Probability.Process.Filtration.StoppingTimeReindex
public import StochLean.Probability.Process.Stopping.LeftContinuousSampling
public import StochLean.Probability.Process.Path.Monotone

/-! # Inverse-clock stopping times and continuous sampled paths

All random times and sampled values use the existing Mathlib owners. Finite
inverse times, clock-level identities and path continuity are proved on a
single event for all levels. The sampled filtration is exactly `F_(T_s)`;
its right continuity, or any martingale conclusion, is not assumed here.
-/

@[expose] public section

open MeasureTheory Filter Set
open scoped NNReal

namespace ProbabilityTheory

variable {Ω : Type*} {A : ℝ≥0 → Ω → ℝ≥0}

noncomputable def clockInverseTime (A : ℝ≥0 → Ω → ℝ≥0) (s : ℝ≥0) : Ω → WithTop ℝ≥0 :=
  hittingAfter A (Ioi s) 0

theorem clockInverseTime_eq_rightClockInverse (A : ℝ≥0 → Ω → ℝ≥0) (s : ℝ≥0) (ω : Ω) :
    clockInverseTime A s ω = rightClockInverse (A · ω) s := rfl

theorem clockInverseTime_monotone (A : ℝ≥0 → Ω → ℝ≥0) : Monotone (clockInverseTime A) :=
  fun _ _ hst ω ↦ rightClockInverse_mono (A · ω) hst

theorem _root_.MeasureTheory.Adapted.isStoppingTime_clockInverseTime
    {mΩ : MeasurableSpace Ω} {P : Measure Ω} {F : Filtration ℝ≥0 mΩ}
    (ha : Adapted F A) (hF : F.IsUsual P) (hc : HasContinuousPaths A P) (s : ℝ≥0) :
    IsStoppingTime F (clockInverseTime A s) :=
  ha.isStoppingTime_hittingAfter_isOpen_of_usual hF hc.hasRightContinuousPaths isOpen_Ioi 0

theorem clockInverseTime_finite_ae {mΩ : MeasurableSpace Ω} {P : Measure Ω}
    (hu : ∀ᵐ ω ∂P, ∀ s, ∃ t, s < A t ω) :
    ∀ᵐ ω ∂P, ∀ s, clockInverseTime A s ω ≠ ⊤ :=
  hu.mono fun _ h s ↦ rightClockInverse_ne_top (h s)

theorem clockInverseTime_value {mΩ : MeasurableSpace Ω} {P : Measure Ω}
    (hc : HasContinuousPaths A P) (hm : HasMonotonePaths A P) (h0 : A 0 =ᵐ[P] 0)
    (hu : ∀ᵐ ω ∂P, ∀ s, ∃ t, s < A t ω) :
    Indistinguishable (fun s ↦ stoppedValue A (clockInverseTime A s)) (fun s _ ↦ s) P := by
  filter_upwards [hc, hm, h0, hu] with ω hcω hmω h0ω huω s
  exact clock_rightClockInverse hcω hmω h0ω (huω s)

theorem hasContinuousPaths_stoppedValue_clockInverseTime
    {E : Type*} [TopologicalSpace E] {mΩ : MeasurableSpace Ω} {P : Measure Ω}
    {X : ℝ≥0 → Ω → E} (hc : HasContinuousPaths A P) (hm : HasMonotonePaths A P)
    (h0 : A 0 =ᵐ[P] 0) (hu : ∀ᵐ ω ∂P, ∀ s, ∃ t, s < A t ω)
    (hx : HasContinuousPaths X P)
    (hf : ∀ᵐ ω ∂P, ∀ s t, A s ω = A t ω → X s ω = X t ω) :
    HasContinuousPaths (fun s ↦ stoppedValue X (clockInverseTime A s)) P := by
  filter_upwards [hc, hm, h0, hu, hx, hf] with ω hcω hmω h0ω huω hxω hfω
  exact continuous_comp_rightClockInverse hcω hmω h0ω huω hxω hfω

theorem stoppedValue_clockInverseTime_comp_clock
    {E : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {X : ℝ≥0 → Ω → E}
    (hc : HasContinuousPaths A P) (hm : HasMonotonePaths A P)
    (h0 : A 0 =ᵐ[P] 0) (hu : ∀ᵐ ω ∂P, ∀ s, ∃ t, s < A t ω)
    (hf : ∀ᵐ ω ∂P, ∀ s t, A s ω = A t ω → X s ω = X t ω) :
    Indistinguishable (fun t ω ↦ stoppedValue X (clockInverseTime A (A t ω)) ω) X P := by
  filter_upwards [hc, hm, h0, hu, hf] with ω hcω hmω h0ω huω hfω t
  exact comp_rightClockInverse_clock hcω hmω h0ω huω hfω t

theorem adapted_stoppedValue_clockInverseTime
    {mΩ : MeasurableSpace Ω} {P : Measure Ω} {F : Filtration ℝ≥0 mΩ}
    {X : ℝ≥0 → Ω → ℝ} (ha : Adapted F A) (hF : F.IsUsual P)
    (hc : HasContinuousPaths A P) (hx : HasContinuousPaths X P) (haX : Adapted F X) :
    Adapted (F.stoppingTimeReindex (clockInverseTime A)
      (ha.isStoppingTime_clockInverseTime hF hc) (clockInverseTime_monotone A))
        (fun s ↦ stoppedValue X (clockInverseTime A s)) := fun s ↦
  haX.measurable_stoppedValue_of_leftContinuous_usual hF
    (hx.mono fun _ hω _ ↦ hω.continuousWithinAt) (ha.isStoppingTime_clockInverseTime hF hc s)

/-- With everywhere clock regularity, the original clock values are stopping
times for the inverse-time filtration, without a strict-increase hypothesis. -/
theorem isStoppingTime_clock_in_inverse_filtration
    {mΩ : MeasurableSpace Ω} {P : Measure Ω} {F : Filtration ℝ≥0 mΩ}
    (ha : Adapted F A) (hF : F.IsUsual P) (hc : ∀ ω, Continuous (A · ω))
    (hm : ∀ ω, Monotone (A · ω)) (h0 : ∀ ω, A 0 ω = 0) (t : ℝ≥0) :
    IsStoppingTime (F.stoppingTimeReindex (clockInverseTime A)
      (ha.isStoppingTime_clockInverseTime hF (Eventually.of_forall hc))
        (clockInverseTime_monotone A)) (fun ω ↦ (A t ω : WithTop ℝ≥0)) := by
  intro s
  have he : {ω | (A t ω : WithTop ℝ≥0) ≤ s} = {ω | (t : WithTop ℝ≥0) ≤ clockInverseTime A s ω} := by
    ext ω
    exact WithTop.coe_le_coe.trans (le_rightClockInverse_iff (hc ω) (hm ω) (h0 ω) s t).symm
  rw [he]
  exact (ha.isStoppingTime_clockInverseTime hF (Eventually.of_forall hc) s).measurableSet_ge' t

end ProbabilityTheory
