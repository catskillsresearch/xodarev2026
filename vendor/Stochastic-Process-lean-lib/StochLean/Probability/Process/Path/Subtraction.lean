/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.Path.Algebra
public import Mathlib.Topology.Algebra.Group.Basic

/-! # Subtraction of cadlag and caglad paths -/

@[expose] public section

open MeasureTheory Filter

namespace ProbabilityTheory

variable {T Ω E : Type*} [LinearOrder T] [TopologicalSpace T]
  [TopologicalSpace E] [Sub E] [ContinuousSub E] {mΩ : MeasurableSpace Ω}
  {P : Measure Ω} {X Y : T → Ω → E}

theorem IsCagladPath.sub {x y : T → E} (hx : IsCagladPath x) (hy : IsCagladPath y) :
    IsCagladPath (x - y) := by
  refine ⟨fun t ↦ (hx.1 t).sub (hy.1 t), ?_⟩
  intro t
  obtain ⟨a, ha⟩ := hx.2 t
  obtain ⟨b, hb⟩ := hy.2 t
  exact ⟨a - b, ha.sub hb⟩

theorem HasCagladPaths.sub (hX : HasCagladPaths X P) (hY : HasCagladPaths Y P) :
    HasCagladPaths (X - Y) P := by
  filter_upwards [hX, hY] with ω hx hy
  exact hx.sub hy

theorem IsCadlagPath.sub [OrderBot T] {x y : T → E}
    (hx : IsCadlagPath x) (hy : IsCadlagPath y) : IsCadlagPath (x - y) := by
  refine ⟨fun t ↦ (hx.1 t).sub (hy.1 t), ?_⟩
  intro t ht
  obtain ⟨a, ha⟩ := hx.2 t ht
  obtain ⟨b, hb⟩ := hy.2 t ht
  exact ⟨a - b, ha.sub hb⟩

theorem HasCadlagPaths.sub [OrderBot T]
    (hX : HasCadlagPaths X P) (hY : HasCadlagPaths Y P) : HasCadlagPaths (X - Y) P := by
  filter_upwards [hX, hY] with ω hx hy
  exact hx.sub hy

end ProbabilityTheory
