/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.Path.Algebra

/-! # Products of regular paths -/

@[expose] public section

open MeasureTheory Filter

namespace ProbabilityTheory

variable {T Ω E : Type*} [LinearOrder T] [TopologicalSpace T]
  [TopologicalSpace E] [Mul E] [ContinuousMul E]
  {mΩ : MeasurableSpace Ω} {P : Measure Ω} {X Y : T → Ω → E}

theorem IsCagladPath.mul {x y : T → E} (hx : IsCagladPath x) (hy : IsCagladPath y) :
    IsCagladPath (x * y) := by
  refine ⟨fun t ↦ (hx.1 t).mul (hy.1 t), ?_⟩
  intro t
  obtain ⟨a, ha⟩ := hx.2 t
  obtain ⟨b, hb⟩ := hy.2 t
  exact ⟨a * b, ha.mul hb⟩

theorem HasCagladPaths.mul (hX : HasCagladPaths X P) (hY : HasCagladPaths Y P) :
    HasCagladPaths (X * Y) P := by
  filter_upwards [hX, hY] with ω hx hy
  exact hx.mul hy

theorem IsCadlagPath.mul [OrderBot T] {x y : T → E}
    (hx : IsCadlagPath x) (hy : IsCadlagPath y) : IsCadlagPath (x * y) := by
  refine ⟨fun t ↦ (hx.1 t).mul (hy.1 t), ?_⟩
  intro t ht
  obtain ⟨a, ha⟩ := hx.2 t ht
  obtain ⟨b, hb⟩ := hy.2 t ht
  exact ⟨a * b, ha.mul hb⟩

theorem HasCadlagPaths.mul [OrderBot T]
    (hX : HasCadlagPaths X P) (hY : HasCadlagPaths Y P) : HasCadlagPaths (X * Y) P := by
  filter_upwards [hX, hY] with ω hx hy
  exact hx.mul hy

end ProbabilityTheory
