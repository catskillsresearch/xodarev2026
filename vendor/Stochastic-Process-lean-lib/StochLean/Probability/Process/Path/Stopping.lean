/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.Path.Cadlag
public import Mathlib.Probability.Process.Stopping

/-! # Stopping preserves common-event path regularity -/

@[expose] public section

open MeasureTheory Filter Set
open scoped NNReal Topology

namespace ProbabilityTheory

variable {E : Type*} [TopologicalSpace E] {x : ℝ≥0 → E}

theorem IsRightContinuousPath.min_const (hx : IsRightContinuousPath x) (T : ℝ≥0) :
    IsRightContinuousPath (fun t ↦ x (min t T)) := by
  intro t
  exact (hx (min t T)).comp (f := fun s ↦ min s T) (x := t)
    (continuous_id.min continuous_const).continuousWithinAt
    (fun _ hu ↦ min_le_min_right T hu)

theorem IsCadlagPath.min_const (hx : IsCadlagPath x) (T : ℝ≥0) :
    IsCadlagPath (fun t ↦ x (min t T)) := by
  refine ⟨hx.1.min_const T, ?_⟩
  intro t ht
  by_cases h : t ≤ T
  · obtain ⟨y, hy⟩ := hx.2 t ht
    refine ⟨y, hy.congr' ?_⟩
    filter_upwards [self_mem_nhdsWithin] with s hs
    rw [min_eq_left (hs.le.trans h)]
  · refine ⟨x T, tendsto_const_nhds.congr' ?_⟩
    have hTt : T < t := lt_of_not_ge h
    filter_upwards [eventually_nhdsWithin_of_eventually_nhds (eventually_gt_nhds hTt)] with s hs
    rw [min_eq_right hs.le]

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
  {X : ℝ≥0 → Ω → E}

omit [TopologicalSpace E] in
theorem Indistinguishable.stoppedValue {Y : ℝ≥0 → Ω → E}
    (h : Indistinguishable X Y P) (τ : Ω → WithTop ℝ≥0) :
    stoppedValue X τ =ᵐ[P] stoppedValue Y τ :=
  h.mono fun _ hω ↦ hω _

omit [TopologicalSpace E] in
theorem Indistinguishable.stoppedProcess {Y : ℝ≥0 → Ω → E}
    (h : Indistinguishable X Y P) (τ : Ω → WithTop ℝ≥0) :
    Indistinguishable (stoppedProcess X τ) (stoppedProcess Y τ) P :=
  h.mono fun _ hω _ ↦ hω _

theorem HasRightContinuousPaths.stoppedProcess (hX : HasRightContinuousPaths X P)
    (τ : Ω → WithTop ℝ≥0) : HasRightContinuousPaths (stoppedProcess X τ) P := by
  filter_upwards [hX] with ω hω
  cases hτ : τ ω with
  | top =>
    simpa only [MeasureTheory.stoppedProcess, hτ, min_eq_left le_top,
      WithTop.untopA, WithTop.untopD_coe] using hω
  | coe T =>
    simpa only [MeasureTheory.stoppedProcess, hτ, ← WithTop.coe_min,
      WithTop.untopA, WithTop.untopD_coe] using hω.min_const T

theorem HasCadlagPaths.stoppedProcess (hX : HasCadlagPaths X P)
    (τ : Ω → WithTop ℝ≥0) : HasCadlagPaths (stoppedProcess X τ) P := by
  filter_upwards [hX] with ω hω
  cases hτ : τ ω with
  | top =>
    simpa only [MeasureTheory.stoppedProcess, hτ, min_eq_left le_top,
      WithTop.untopA, WithTop.untopD_coe] using hω
  | coe T =>
    simpa only [MeasureTheory.stoppedProcess, hτ, ← WithTop.coe_min,
      WithTop.untopA, WithTop.untopD_coe] using hω.min_const T

theorem HasContinuousPaths.stoppedProcess (hX : HasContinuousPaths X P)
    (τ : Ω → WithTop ℝ≥0) : HasContinuousPaths (stoppedProcess X τ) P := by
  filter_upwards [hX] with ω hω
  cases hτ : τ ω with
  | top =>
    simpa only [MeasureTheory.stoppedProcess, hτ, min_eq_left le_top,
      WithTop.untopA, WithTop.untopD_coe] using hω
  | coe T =>
    simpa only [MeasureTheory.stoppedProcess, hτ, ← WithTop.coe_min,
      WithTop.untopA, WithTop.untopD_coe, Function.comp_def, id_eq, IsContinuousPath] using
      hω.comp (continuous_id.min (continuous_const (y := T)))

end ProbabilityTheory
