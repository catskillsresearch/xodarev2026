/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.Path.Caglad
public import StochLean.Probability.Process.Measurability.Predictable
public import Mathlib.Probability.Process.Stopping

/-! # Cutting an integrand off after a stopping time

Unlike a stopped process, the cutoff is zero strictly after the stopping time.
The closed endpoint preserves the stopping jump and the initial value.
-/

@[expose] public section

open MeasureTheory Filter Set
open scoped NNReal Topology

namespace ProbabilityTheory

theorem IsCagladPath.indicator_Iic {x : ℝ≥0 → ℝ} (hx : IsCagladPath x) (T : ℝ≥0) :
    IsCagladPath ((Iic T).indicator x) := by
  constructor
  · intro t
    by_cases ht : t ≤ T
    · change Tendsto _ (𝓝[≤] t) _
      rw [indicator_of_mem (s := Iic T) (a := t) ht]
      apply (hx.1 t).congr'
      filter_upwards [self_mem_nhdsWithin] with u hu
      exact (indicator_of_mem (s := Iic T) (a := u)
        (show u ≤ T from (show u ≤ t from hu).trans ht) x).symm
    · change Tendsto _ (𝓝[≤] t) _
      rw [indicator_of_notMem (s := Iic T) (a := t) ht]
      apply tendsto_const_nhds.congr'
      filter_upwards [nhdsWithin_le_nhds (Ioi_mem_nhds (lt_of_not_ge ht))] with u hu
      exact (indicator_of_notMem (s := Iic T) (a := u)
        (show ¬u ≤ T from not_le_of_gt hu) x).symm
  · intro t
    by_cases ht : t < T
    · obtain ⟨y, hy⟩ := hx.2 t
      refine ⟨y, hy.congr' ?_⟩
      filter_upwards [nhdsWithin_le_nhds (Iio_mem_nhds ht)] with u hu
      exact (indicator_of_mem (s := Iic T) (a := u)
        (show u ≤ T from (show u < T from hu).le) x).symm
    · refine ⟨0, tendsto_const_nhds.congr' ?_⟩
      filter_upwards [self_mem_nhdsWithin] with u hu
      exact (indicator_of_notMem (s := Iic T) (a := u)
        (show ¬u ≤ T from not_le_of_gt ((le_of_not_gt ht).trans_lt (show t < u from hu))) x).symm

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {F : Filtration ℝ≥0 mΩ}

noncomputable def cutoffIntegrand (H : ℝ≥0 → Ω → ℝ) (τ : Ω → WithTop ℝ≥0)
    (t : ℝ≥0) (ω : Ω) : ℝ :=
  if (t : WithTop ℝ≥0) ≤ τ ω then H t ω else 0

@[simp] theorem cutoffIntegrand_zero (H : ℝ≥0 → Ω → ℝ) (τ : Ω → WithTop ℝ≥0) (ω : Ω) :
    cutoffIntegrand H τ 0 ω = H 0 ω := by
  simp [cutoffIntegrand]

@[simp] theorem cutoffIntegrand_top (H : ℝ≥0 → Ω → ℝ) :
    cutoffIntegrand H (fun _ ↦ ⊤) = H := by
  funext t ω
  simp only [cutoffIntegrand, le_top, if_true]

theorem adapted_cutoffIntegrand {H : ℝ≥0 → Ω → ℝ} (hH : Adapted F H)
    {τ : Ω → WithTop ℝ≥0} (hτ : IsStoppingTime F τ) : Adapted F (cutoffIntegrand H τ) :=
  fun t ↦ Measurable.ite (hτ.measurableSet_ge t) (hH t) measurable_const

theorem isCagladPath_cutoffIntegrand {H : ℝ≥0 → Ω → ℝ}
    (hH : ∀ ω, IsCagladPath (fun t ↦ H t ω)) (τ : Ω → WithTop ℝ≥0) (ω : Ω) :
    IsCagladPath (fun t ↦ cutoffIntegrand H τ t ω) := by
  cases hτ : τ ω with
  | top => simpa only [cutoffIntegrand, hτ, le_top, if_true] using hH ω
  | coe T =>
      have h := (hH ω).indicator_Iic T
      change IsCagladPath (fun t ↦ if t ≤ T then H t ω else 0) at h
      simpa only [cutoffIntegrand, hτ, WithTop.coe_le_coe] using h

theorem isStronglyPredictable_cutoffIntegrand {H : ℝ≥0 → Ω → ℝ}
    (hHa : Adapted F H) (hHc : ∀ ω, IsCagladPath (fun t ↦ H t ω))
    {τ : Ω → WithTop ℝ≥0} (hτ : IsStoppingTime F τ) :
    IsStronglyPredictable F (cutoffIntegrand H τ) :=
  (adapted_cutoffIntegrand hHa hτ).isStronglyPredictable_of_leftContinuous
    (fun ω ↦ (isCagladPath_cutoffIntegrand hHc τ ω).1)

end ProbabilityTheory
