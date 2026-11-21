/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.Path.Monotone
public import Mathlib.Probability.Martingale.Basic
public import Mathlib.Probability.Process.Stopping

/-! # Integrable adapted increasing processes are submartingales -/

@[expose] public section

open MeasureTheory Filter Set
open scoped NNReal

namespace ProbabilityTheory

theorem HasMonotonePaths.indicator {ι Ω : Type*} [Preorder ι]
    {mΩ : MeasurableSpace Ω} {P : Measure Ω} {X : ι → Ω → ℝ}
    (hX : HasMonotonePaths X P) (A : Set Ω) :
    HasMonotonePaths (fun t ↦ A.indicator (X t)) P := by
  filter_upwards [hX] with ω hω s t hst
  by_cases hA : ω ∈ A
  · simpa only [indicator_of_mem hA] using hω hst
  · simp only [indicator_of_notMem hA, le_refl]

theorem HasMonotonePaths.stoppedProcess {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {P : Measure Ω} {X : ℝ≥0 → Ω → ℝ}
    (hX : HasMonotonePaths X P) (τ : Ω → WithTop ℝ≥0) :
    HasMonotonePaths (stoppedProcess X τ) P := by
  filter_upwards [hX] with ω hω s t hst
  cases ht : τ ω with
  | top => simpa only [MeasureTheory.stoppedProcess, ht, min_eq_left le_top,
      WithTop.untopA, WithTop.untopD_coe] using hω hst
  | coe u => simpa only [MeasureTheory.stoppedProcess, ht, ← WithTop.coe_min,
      WithTop.untopA, WithTop.untopD_coe] using hω (min_le_min_right u hst)

theorem HasMonotonePaths.submartingale {ι Ω : Type*} [Preorder ι]
    {mΩ : MeasurableSpace Ω} {P : Measure Ω} {F : Filtration ι mΩ}
    [SigmaFiniteFiltration P F] {X : ι → Ω → ℝ}
    (hX : HasMonotonePaths X P) (ha : Adapted F X)
    (hi : ∀ t, Integrable (X t) P) : Submartingale X F P := by
  apply submartingale_of_setIntegral_le ha.stronglyAdapted hi
  intro s t hst A _
  exact setIntegral_mono_ae (hi s).integrableOn (hi t).integrableOn
    (hX.mono fun _ hω ↦ hω hst)

end ProbabilityTheory
