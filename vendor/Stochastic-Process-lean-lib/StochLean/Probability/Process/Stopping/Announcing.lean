/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.Stopping.BeforeSigmaOrder
public import StochLean.Probability.Process.Filtration.Usual

/-! # Announcing sequences and predictable stopping times

The source Protter III.2 convention allows zero and infinite lifetimes. An
announcing sequence is pointwise increasing, strictly below the lifetime on
its positive event, and converges almost surely. In particular, almost-sure
convergence is not silently replaced by everywhere convergence.
-/

@[expose] public section

open MeasureTheory Filter
open scoped NNReal Topology

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

/-- Witness relation from Protter III.2. It does not choose an announcing sequence. -/
structure IsAnnouncingSequence (F : Filtration ℝ≥0 mΩ) (P : Measure Ω)
    (τ : Ω → WithTop ℝ≥0) (σ : ℕ → Ω → WithTop ℝ≥0) : Prop where
  isStoppingTime : ∀ n, IsStoppingTime F (σ n)
  monotone : ∀ ω, Monotone (fun n ↦ σ n ω)
  strict : ∀ n ω, 0 < τ ω → σ n ω < τ ω
  tendsto : ∀ᵐ ω ∂P, Tendsto (fun n ↦ σ n ω) atTop (𝓝 (τ ω))

/-- Predictability of a stopping time is existence of source announcing data,
not an identification with accessibility or predictability of an arbitrary graph. -/
def IsPredictableStoppingTime (F : Filtration ℝ≥0 mΩ) (τ : Ω → WithTop ℝ≥0)
    (P : Measure Ω) : Prop :=
  IsStoppingTime F τ ∧ ∃ σ, IsAnnouncingSequence F P τ σ

namespace IsAnnouncingSequence

variable {F : Filtration ℝ≥0 mΩ} {P : Measure Ω}
  {τ : Ω → WithTop ℝ≥0} {σ : ℕ → Ω → WithTop ℝ≥0}

theorem ae_le (h : IsAnnouncingSequence F P τ σ) :
    ∀ᵐ ω ∂P, ∀ n, σ n ω ≤ τ ω := by
  filter_upwards [h.tendsto] with ω hω n
  exact (h.monotone ω).ge_of_tendsto hω n

theorem ae_eq_zero_of_zero (h : IsAnnouncingSequence F P τ σ) :
    ∀ᵐ ω ∂P, τ ω = 0 → ∀ n, σ n ω = 0 := by
  filter_upwards [h.ae_le] with ω hω ht n
  exact le_antisymm (ht ▸ hω n) bot_le

theorem predictable (h : IsAnnouncingSequence F P τ σ) (hτ : IsStoppingTime F τ) :
    IsPredictableStoppingTime F τ P := ⟨hτ, σ, h⟩

end IsAnnouncingSequence

end ProbabilityTheory
