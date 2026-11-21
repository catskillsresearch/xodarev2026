/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.Path.Monotone
public import Mathlib.Topology.EMetricSpace.BoundedVariation

/-! # Finite variation on one common path event

The deterministic owners remain Mathlib's bounded and locally bounded variation.
Local finite variation and finite total variation on the half-line are distinct.
Cadlag paths and adaptedness are separate hypotheses, not implicit fields.
-/

@[expose] public section

open MeasureTheory Filter Set
open scoped NNReal ENNReal

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

def HasFiniteVariationPaths (X : ℝ≥0 → Ω → ℝ) (P : Measure Ω := by volume_tac) : Prop :=
  ∀ᵐ ω ∂P, LocallyBoundedVariationOn (fun t ↦ X t ω) univ

def HasFiniteTotalVariationPaths (X : ℝ≥0 → Ω → ℝ) (P : Measure Ω := by volume_tac) : Prop :=
  ∀ᵐ ω ∂P, BoundedVariationOn (fun t ↦ X t ω) univ

variable {X Y : ℝ≥0 → Ω → ℝ} {P : Measure Ω}

theorem hasFiniteVariationPaths_iff_ae_forall_horizon :
    HasFiniteVariationPaths X P ↔ ∀ᵐ ω ∂P, ∀ T, BoundedVariationOn (fun t ↦ X t ω) (Icc 0 T) := by
  constructor
  · intro h
    filter_upwards [h] with ω hω T
    simpa only [univ_inter] using hω 0 T (mem_univ _) (mem_univ _)
  · intro h
    filter_upwards [h] with ω hω a b _ _
    exact (hω b).mono (fun _ hx ↦ ⟨bot_le, hx.2.2⟩)

theorem HasFiniteVariationPaths.congr (hXY : Indistinguishable X Y P)
    (hX : HasFiniteVariationPaths X P) : HasFiniteVariationPaths Y P := by
  filter_upwards [hXY, hX] with ω hω hfv
  simpa only [hω] using hfv

theorem HasFiniteTotalVariationPaths.hasFiniteVariationPaths
    (hX : HasFiniteTotalVariationPaths X P) :
    HasFiniteVariationPaths X P :=
  hX.mono fun _ hω ↦ hω.locallyBoundedVariationOn

theorem HasMonotonePaths.hasFiniteVariationPaths (hX : HasMonotonePaths X P) :
    HasFiniteVariationPaths X P :=
  hX.mono fun _ hω ↦ (hω.monotoneOn univ).locallyBoundedVariationOn

end ProbabilityTheory
