/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.Path.Algebra
public import Mathlib.Probability.Process.Adapted

/-! # Initial-event masks of adapted processes

An initial measurable event preserves adaptedness. Path properties and
indistinguishability need no measurability assumption on the masking event.
-/

@[expose] public section

open MeasureTheory Set

namespace MeasureTheory

theorem Adapted.indicator_initial {T Ω E : Type*} [Preorder T] [OrderBot T]
    {mΩ : MeasurableSpace Ω} [MeasurableSpace E] [Zero E]
    {F : Filtration T mΩ} {X : T → Ω → E} (hX : Adapted F X)
    {s : Set Ω} (hs : MeasurableSet[F ⊥] s) :
    Adapted F (fun t ↦ s.indicator (X t)) :=
  fun t ↦ (hX t).indicator (F.mono bot_le s hs)

end MeasureTheory

namespace ProbabilityTheory

variable {T Ω E : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [Zero E]
  {X Y : T → Ω → E}

theorem Indistinguishable.indicator (hXY : Indistinguishable X Y P) (s : Set Ω) :
    Indistinguishable (fun t ↦ s.indicator (X t)) (fun t ↦ s.indicator (Y t)) P := by
  filter_upwards [hXY] with ω hω t
  by_cases hs : ω ∈ s
  · simpa only [Set.indicator_of_mem hs] using hω t
  · simp only [Set.indicator_of_notMem hs]

theorem HasCagladPaths.indicator [LinearOrder T] [TopologicalSpace T]
    [TopologicalSpace E] (hX : HasCagladPaths X P) (s : Set Ω) :
    HasCagladPaths (fun t ↦ s.indicator (X t)) P := by
  filter_upwards [hX] with ω hω
  by_cases hs : ω ∈ s
  · simpa only [Set.indicator_of_mem hs] using hω
  · simp only [Set.indicator_of_notMem hs]
    exact IsContinuousPath.isCagladPath continuous_const

end ProbabilityTheory
