/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.StationaryIndependentIncrements.CountableStopping
public import StochLean.Probability.Process.Stopping.ConditionalFiniteSampling
public import Mathlib.Topology.ContinuousMap.Bounded.Basic

/-! # Stationary increments after a genuinely finite stopping time

Actual deterministic past independence and stationarity give the constant
conditional projection of each bounded continuous increment test. The proved
dominated right-continuous sampling theorem passes to the original stopped
field at any genuinely finite stopping time, without a deterministic bound.

The process and filtration remain unchanged. No random-time independence,
random-lag substitution, Markov certificate, or arbitrary enlargement is
assumed. Initial values are retained in the reference increment.
-/

@[expose] public section

open MeasureTheory Filter Set
open scoped NNReal Topology BoundedContinuousFunction

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
  {F : Filtration ℝ≥0 mΩ} {X : ℝ≥0 → Ω → ℝ}

/-- A bounded continuous test of an actual increment after any genuinely
finite stopping time has its stationary mean given the original stopped field.
Common-event right continuity suffices; left limits and usualness are not needed. -/
theorem HasStationaryIncrements.condExp_increment_after
    (hs : HasStationaryIncrements X P) (hXm : ∀ s, Measurable (X s))
    (hr : HasRightContinuousPaths X P)
    (hi : ∀ s t, s ≤ t → Indep (F s) (MeasurableSpace.comap
      (fun ω ↦ X t ω - X s ω) inferInstance) P)
    (τ : FiniteStoppingTime F) (u : ℝ≥0) (f : ℝ →ᵇ ℝ) :
    P[(fun ω ↦ f (X (τ ω + u) ω - X (τ ω) ω)) | τ.measurableSpace] =ᵐ[P]
      fun _ ↦ ∫ ω, f (X u ω - X 0 ω) ∂P := by
  let V (s : ℝ≥0) (ω : Ω) := f (X (s + u) ω - X s ω)
  have hmV (s : ℝ≥0) : Measurable (V s) :=
    f.continuous.measurable.comp ((hXm (s + u)).sub (hXm s))
  have hrV : HasRightContinuousPaths V P := by
    filter_upwards [hr] with ω hω
    intro s
    have htime : ContinuousWithinAt (fun v : ℝ≥0 ↦ v + u) (Ici s) s :=
      continuousWithinAt_id.add continuousWithinAt_const
    have hshift : ContinuousWithinAt (fun v ↦ X (v + u) ω) (Ici s) s :=
      (hω (s + u)).comp (f := fun v : ℝ≥0 ↦ v + u) (x := s)
        htime (by
          intro v hv
          change s + u ≤ v + u
          exact _root_.add_le_add hv le_rfl)
    exact f.continuous.continuousAt.comp_continuousWithinAt (hshift.sub (hω s))
  apply τ.sample_condExp_const_of_dominated_rightContinuous hmV hrV
    (integrable_const ‖f‖) (ae_of_all _ fun _ _ ↦ f.norm_coe_le_norm _) _
  intro s
  have hcount : (range (FiniteStoppingTime.const F s)).Countable := by
    apply (countable_singleton s).mono
    rintro y ⟨ω, rfl⟩
    exact mem_singleton s
  have h := hs.condExp_increment_after_countable hXm hi
    (FiniteStoppingTime.const F s) hcount u f f.continuous.measurable ‖f‖
    (fun x ↦ f.norm_coe_le_norm x)
  simpa only [FiniteStoppingTime.const_apply, FiniteStoppingTime.measurableSpace,
    FiniteStoppingTime.const, IsStoppingTime.measurableSpace_const] using h

end ProbabilityTheory
