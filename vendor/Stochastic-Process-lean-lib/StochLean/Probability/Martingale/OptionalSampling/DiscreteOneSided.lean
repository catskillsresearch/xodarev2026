/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Martingale.OptionalSampling.CountableRangeOneSided
public import Mathlib.Probability.Martingale.OptionalStopping

/-! # Conditional one-sided optional sampling in discrete time

The existing stopped-submartingale theorem and countable-range terminal
comparison yield two-stopping-time conditional inequalities. Both stopping
sigma-fields and stopped values are the native Mathlib owners.
-/

@[expose] public section

open Filter Set

namespace MeasureTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsFiniteMeasure P]
  {F : Filtration ℕ mΩ} {X : ℕ → Ω → ℝ} {σ τ : Ω → WithTop ℕ}

theorem Submartingale.stoppedValue_ae_le_condExp_of_le
    (hX : Submartingale X F P) (hσ : IsStoppingTime F σ) (hτ : IsStoppingTime F τ)
    (hle : ∀ ω, σ ω ≤ τ ω) {N : ℕ} (hb : ∀ ω, τ ω ≤ N) :
    stoppedValue X σ ≤ᵐ[P] P[stoppedValue X τ | hσ.measurableSpace] := by
  have hσb (ω) : σ ω ≤ N := (hle ω).trans (hb ω)
  have hσf (ω) : σ ω ≠ ⊤ := ne_top_of_le_ne_top (by simp) (hσb ω)
  have h := Submartingale.stoppedValue_ae_le_condExp_of_le_const_of_countable_range
    (T := N) (hX.stoppedProcess hτ) hσ hσb (Set.to_countable _)
  have hs : stoppedValue (stoppedProcess X τ) σ = stoppedValue X σ := by
    funext ω
    rw [stoppedValue_stoppedProcess_apply (hσf ω)]
    simp only [min_eq_left (hle _)]
  have ht : stoppedProcess X τ N = stoppedValue X τ := by
    funext ω
    exact stoppedProcess_eq_of_ge (hb ω)
  rwa [hs, ht] at h

theorem Supermartingale.condExp_stoppedValue_ae_le_of_le
    (hX : Supermartingale X F P) (hσ : IsStoppingTime F σ) (hτ : IsStoppingTime F τ)
    (hle : ∀ ω, σ ω ≤ τ ω) {N : ℕ} (hb : ∀ ω, τ ω ≤ N) :
    P[stoppedValue X τ | hσ.measurableSpace] ≤ᵐ[P] stoppedValue X σ := by
  have h := hX.neg.stoppedValue_ae_le_condExp_of_le hσ hτ hle hb
  filter_upwards [h, condExp_neg (stoppedValue X τ) hσ.measurableSpace] with ω hω heω
  simpa only [stoppedValue_neg, Pi.neg_apply, heω, neg_le_neg_iff] using hω

end MeasureTheory
