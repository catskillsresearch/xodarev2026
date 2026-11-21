/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.Path.RightContinuous

/-! # Simultaneous order for right-continuous processes

Coordinatewise almost-sure inequalities become pathwise inequalities on one
full-measure event. Right continuity is essential: an uncountable intersection
of arbitrary coordinate full-measure events would not justify this conclusion.
-/

@[expose] public section

open MeasureTheory Filter Set
open scoped Topology

namespace ProbabilityTheory

variable {T Ω : Type*} {mΩ : MeasurableSpace Ω}
  [LinearOrder T] [TopologicalSpace T] [OrderTopology T] [DenselyOrdered T] [NoMaxOrder T]
  [FirstCountableTopology T] [TopologicalSpace.SeparableSpace T] [Nonempty T]
  {X Y : T → Ω → ℝ} {P : Measure Ω}

theorem HasRightContinuousPaths.ae_forall_le_of_forall_ae_le
    (hX : HasRightContinuousPaths X P) (hY : HasRightContinuousPaths Y P)
    (hle : ∀ t, X t ≤ᵐ[P] Y t) : ∀ᵐ ω ∂P, ∀ t, X t ω ≤ Y t ω := by
  have hdense : ∀ᵐ ω ∂P, ∀ n, X (TopologicalSpace.denseSeq T n) ω ≤
      Y (TopologicalSpace.denseSeq T n) ω :=
    ae_all_iff.mpr (fun n ↦ hle (TopologicalSpace.denseSeq T n))
  filter_upwards [hdense, hX, hY] with ω hω hXω hYω
  intro t
  have hD : Dense (range (TopologicalSpace.denseSeq T)) :=
    TopologicalSpace.denseRange_denseSeq T
  obtain ⟨u, _, hu, hlim⟩ := hD.exists_seq_strictAnti_tendsto t
  have hwithin : Tendsto u atTop (𝓝[≥] t) :=
    tendsto_nhdsWithin_iff.mpr
      ⟨hlim, Eventually.of_forall fun n ↦ (hu n).1.le⟩
  refine le_of_tendsto_of_tendsto' ((hXω t).tendsto.comp hwithin)
    ((hYω t).tendsto.comp hwithin) (fun n ↦ ?_)
  obtain ⟨k, hk⟩ := (hu n).2
  change X (u n) ω ≤ Y (u n) ω
  rw [← hk]
  exact hω k

end ProbabilityTheory
