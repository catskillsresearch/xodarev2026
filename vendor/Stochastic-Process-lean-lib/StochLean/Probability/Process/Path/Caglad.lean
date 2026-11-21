/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.Path.Cadlag

/-! # Common-event càglàd paths

Chapter II integrands have left-continuous paths with finite right limits.
The existential right limit does not select a default outside this domain.
-/

@[expose] public section

open MeasureTheory Filter Set
open scoped Topology

namespace ProbabilityTheory

variable {T Ω E : Type*} [LinearOrder T] [TopologicalSpace T]
  [TopologicalSpace E] {mΩ : MeasurableSpace Ω} {P : Measure Ω}

def IsCagladPath (x : T → E) : Prop :=
  IsLeftContinuousPath x ∧ ∀ t, ∃ y : E, Tendsto x (nhdsWithin t (Ioi t)) (𝓝 y)

def HasCagladPaths (X : T → Ω → E) (P : Measure Ω := by volume_tac) : Prop :=
  ∀ᵐ ω ∂P, IsCagladPath fun t ↦ X t ω

theorem IsContinuousPath.isCagladPath {x : T → E} (hx : IsContinuousPath x) :
    IsCagladPath x :=
  ⟨hx.isLeftContinuousPath, fun t ↦ ⟨x t, hx.continuousAt.continuousWithinAt⟩⟩

theorem HasContinuousPaths.hasCagladPaths {X : T → Ω → E}
    (hX : HasContinuousPaths X P) : HasCagladPaths X P :=
  hX.mono fun _ hω ↦ hω.isCagladPath

theorem HasCagladPaths.hasLeftContinuousPaths {X : T → Ω → E}
    (hX : HasCagladPaths X P) : HasLeftContinuousPaths X P := hX.mono fun _ ↦ And.left

theorem HasCagladPaths.congr {X Y : T → Ω → E}
    (hXY : Indistinguishable X Y P) (hX : HasCagladPaths X P) : HasCagladPaths Y P := by
  filter_upwards [hXY, hX] with ω hω hreg
  have heq : (fun t ↦ X t ω) = fun t ↦ Y t ω := funext hω
  rwa [← heq]

end ProbabilityTheory
