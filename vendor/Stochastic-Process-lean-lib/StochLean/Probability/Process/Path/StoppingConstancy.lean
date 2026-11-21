/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.Path.Stopping

/-! # Closed stochastic-interval constancy and equality of stopped paths

Only finite evaluations are used. In particular an infinite endpoint never
acquires a value by applying `untopA` to infinity.
-/

@[expose] public section

open MeasureTheory
open scoped NNReal

namespace ProbabilityTheory

variable {Ω E : Type*} {X : ℝ≥0 → Ω → E} {σ τ : Ω → WithTop ℝ≥0} {ω : Ω}

theorem eq_on_stopping_interval_of_stoppedProcess_eq
    (he : ∀ t, MeasureTheory.stoppedProcess X τ t ω =
      MeasureTheory.stoppedProcess X σ t ω) :
    ∀ s t : ℝ≥0, σ ω ≤ s → (s : WithTop ℝ≥0) ≤ τ ω →
      σ ω ≤ t → (t : WithTop ℝ≥0) ≤ τ ω → X s ω = X t ω := by
  intro s t hσs hsτ hσt htτ
  have hs := he s
  have ht := he t
  simp only [MeasureTheory.stoppedProcess, min_eq_left hsτ, min_eq_right hσs,
    WithTop.untopA, WithTop.untopD_coe] at hs
  simp only [MeasureTheory.stoppedProcess, min_eq_left htτ, min_eq_right hσt,
    WithTop.untopA, WithTop.untopD_coe] at ht
  exact hs.trans ht.symm

theorem stoppedProcess_eq_of_eq_on_stopping_interval
    (hle : σ ω ≤ τ ω)
    (he : ∀ s t : ℝ≥0, σ ω ≤ s → (s : WithTop ℝ≥0) ≤ τ ω →
      σ ω ≤ t → (t : WithTop ℝ≥0) ≤ τ ω → X s ω = X t ω) :
    ∀ t, MeasureTheory.stoppedProcess X τ t ω =
      MeasureTheory.stoppedProcess X σ t ω := by
  intro t
  by_cases ht : (t : WithTop ℝ≥0) ≤ σ ω
  · simp only [MeasureTheory.stoppedProcess, min_eq_left ht, min_eq_left (ht.trans hle)]
  · have hσt : σ ω ≤ t := le_of_not_ge ht
    have hn : σ ω ≠ ⊤ := ne_top_of_le_ne_top WithTop.coe_ne_top hσt
    have hmin : min (t : WithTop ℝ≥0) (τ ω) ≠ ⊤ :=
      ne_top_of_le_ne_top WithTop.coe_ne_top (min_le_left _ _)
    have ha : ((σ ω).untopA : WithTop ℝ≥0) = σ ω := by
      rw [WithTop.untopA_eq_untop hn, WithTop.coe_untop]
    have hb : ((min (t : WithTop ℝ≥0) (τ ω)).untopA : WithTop ℝ≥0) =
        min (t : WithTop ℝ≥0) (τ ω) := by
      rw [WithTop.untopA_eq_untop hmin, WithTop.coe_untop]
    change X (min (t : WithTop ℝ≥0) (τ ω)).untopA ω =
      X (min (t : WithTop ℝ≥0) (σ ω)).untopA ω
    rw [min_eq_right hσt]
    exact he _ _ (by rw [hb]; exact le_min hσt hle)
      (by rw [hb]; exact min_le_right _ _) (by rw [ha]) (by rw [ha]; exact hle)

theorem stoppedProcess_eq_iff_eq_on_stopping_interval (hle : σ ω ≤ τ ω) :
    (∀ t, MeasureTheory.stoppedProcess X τ t ω = MeasureTheory.stoppedProcess X σ t ω) ↔
      ∀ s t : ℝ≥0, σ ω ≤ s → (s : WithTop ℝ≥0) ≤ τ ω →
        σ ω ≤ t → (t : WithTop ℝ≥0) ≤ τ ω → X s ω = X t ω :=
  ⟨eq_on_stopping_interval_of_stoppedProcess_eq,
    stoppedProcess_eq_of_eq_on_stopping_interval hle⟩

end ProbabilityTheory
