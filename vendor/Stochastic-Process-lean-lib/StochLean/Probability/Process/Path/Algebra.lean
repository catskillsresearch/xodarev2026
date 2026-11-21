/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.Path.Caglad
public import Mathlib.Topology.Algebra.Monoid

/-! # Continuous operations on cadlag and caglad paths

The process statements intersect finitely many common full-measure events.
-/

@[expose] public section

open MeasureTheory Filter Set
open scoped Topology

namespace ProbabilityTheory

variable {T Ω E G : Type*} [LinearOrder T] [TopologicalSpace T]
  [TopologicalSpace E] [TopologicalSpace G] {mΩ : MeasurableSpace Ω}
  {P : Measure Ω} {X Y : T → Ω → E}

theorem IsCagladPath.continuous_comp {x : T → E} (hx : IsCagladPath x)
    {f : E → G} (hf : Continuous f) : IsCagladPath (f ∘ x) := by
  refine ⟨fun t ↦ hf.continuousAt.comp_continuousWithinAt (hx.1 t), ?_⟩
  intro t
  obtain ⟨y, hy⟩ := hx.2 t
  exact ⟨f y, hf.continuousAt.tendsto.comp hy⟩

theorem HasCagladPaths.continuous_comp (hX : HasCagladPaths X P)
    {f : E → G} (hf : Continuous f) : HasCagladPaths (fun t ω ↦ f (X t ω)) P :=
  hX.mono fun _ hω ↦ hω.continuous_comp hf

theorem IsCagladPath.add [Add E] [ContinuousAdd E] {x y : T → E}
    (hx : IsCagladPath x) (hy : IsCagladPath y) : IsCagladPath (x + y) := by
  refine ⟨fun t ↦ (hx.1 t).add (hy.1 t), ?_⟩
  intro t
  obtain ⟨a, ha⟩ := hx.2 t
  obtain ⟨b, hb⟩ := hy.2 t
  exact ⟨a + b, ha.add hb⟩

theorem HasCagladPaths.add [Add E] [ContinuousAdd E]
    (hX : HasCagladPaths X P) (hY : HasCagladPaths Y P) : HasCagladPaths (X + Y) P := by
  filter_upwards [hX, hY] with ω hx hy
  exact hx.add hy

variable [OrderBot T]

theorem IsCadlagPath.continuous_comp {x : T → E} (hx : IsCadlagPath x)
    {f : E → G} (hf : Continuous f) : IsCadlagPath (f ∘ x) := by
  refine ⟨fun t ↦ hf.continuousAt.comp_continuousWithinAt (hx.1 t), ?_⟩
  intro t ht
  obtain ⟨y, hy⟩ := hx.2 t ht
  exact ⟨f y, hf.continuousAt.tendsto.comp hy⟩

theorem HasCadlagPaths.continuous_comp (hX : HasCadlagPaths X P)
    {f : E → G} (hf : Continuous f) : HasCadlagPaths (fun t ω ↦ f (X t ω)) P :=
  hX.mono fun _ hω ↦ hω.continuous_comp hf

theorem IsCadlagPath.add [Add E] [ContinuousAdd E] {x y : T → E}
    (hx : IsCadlagPath x) (hy : IsCadlagPath y) : IsCadlagPath (x + y) := by
  refine ⟨fun t ↦ (hx.1 t).add (hy.1 t), ?_⟩
  intro t ht
  obtain ⟨a, ha⟩ := hx.2 t ht
  obtain ⟨b, hb⟩ := hy.2 t ht
  exact ⟨a + b, ha.add hb⟩

theorem IsCadlagPath.finset_sum [AddCommMonoid E] [ContinuousAdd E]
    {ι : Type*} (s : Finset ι) (f : ι → T → E)
    (hf : ∀ i ∈ s, IsCadlagPath (f i)) : IsCadlagPath (fun t ↦ ∑ i ∈ s, f i t) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simpa using (IsContinuousPath.isCadlagPath
      (continuous_const : Continuous (fun _ : T ↦ (0 : E))))
  | @insert i s hi ih =>
    simp only [Finset.sum_insert hi]
    exact (hf i (Finset.mem_insert_self i s)).add
      (ih (fun j hj ↦ hf j (Finset.mem_insert_of_mem hj)))

theorem HasCadlagPaths.add [Add E] [ContinuousAdd E]
    (hX : HasCadlagPaths X P) (hY : HasCadlagPaths Y P) : HasCadlagPaths (X + Y) P := by
  filter_upwards [hX, hY] with ω hx hy
  exact hx.add hy

theorem HasCadlagPaths.indicator [Zero E] (hX : HasCadlagPaths X P) (s : Set Ω) :
    HasCadlagPaths (fun t ↦ s.indicator (X t)) P := by
  filter_upwards [hX] with ω hω
  by_cases h : ω ∈ s
  · simpa only [Set.indicator_of_mem h] using hω
  · simp only [Set.indicator_of_notMem h]
    exact IsContinuousPath.isCadlagPath continuous_const

end ProbabilityTheory
