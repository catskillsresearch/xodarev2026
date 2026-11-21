/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Martingale.Inequalities.OneSidedWeakCountable
public import StochLean.Probability.Martingale.Inequalities.UpcrossingGlobalL1

/-! # Local first moments and finite crossings before regularization

Deterministic clipping at a finite horizon provides a global first-moment
bound for the clipped one-sided martingale. The existing upcrossing estimate
then gives one event of finite rational-level counts on every integer horizon.
No path continuity, usual conditions, UI or L2 assumptions occur here.
-/

@[expose] public section

open StochLean MeasureTheory Filter Set
open scoped NNReal ENNReal

namespace MeasureTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsFiniteMeasure P]
  {F : Filtration ℝ≥0 mΩ} {X : ℝ≥0 → Ω → ℝ} {t T : ℝ≥0}

theorem Supermartingale.integral_norm_le_endpoints (hX : Supermartingale X F P)
    (ht : t ≤ T) :
    (∫ ω, ‖X t ω‖ ∂P) ≤ (∫ ω, X 0 ω ∂P) + 2 * (∫ ω, ‖X T ω‖ ∂P) := by
  have he := integral_mono_ae integrable_condExp (hX.integrable 0)
    (hX.condExp_ae_le (show (0 : ℝ≥0) ≤ t from bot_le))
  rw [integral_condExp (F.le 0)] at he
  exact ((hX.integrable t).integral_norm_le_of_condExp_le (hX.condExp_ae_le ht)).trans
    (add_le_add he le_rfl)

theorem Submartingale.integral_norm_le_endpoints (hX : Submartingale X F P)
    (ht : t ≤ T) :
    (∫ ω, ‖X t ω‖ ∂P) ≤ -(∫ ω, X 0 ω ∂P) + 2 * (∫ ω, ‖X T ω‖ ∂P) := by
  simpa only [Pi.neg_apply, norm_neg, integral_neg] using hX.neg.integral_norm_le_endpoints ht

/-- Countably many horizons and rational level pairs share one full-measure event. -/
theorem Submartingale.ae_all_rat_denseUpcrossings_min_lt_top
    (hX : Submartingale X F P) :
    ∀ᵐ ω ∂P, ∀ N : ℕ, ∀ a b : ℚ, a < b →
      denseUpcrossings a b (fun t ↦ X (min t (N : ℝ≥0))) ω < ⊤ := by
  apply ae_all_iff.mpr
  intro N
  have he : Monotone (fun t : ℝ≥0 ↦ min t (N : ℝ≥0)) := fun _ _ h ↦ min_le_min h le_rfl
  have hc := hX.reindex (fun t ↦ min t (N : ℝ≥0)) he
  exact hc.ae_all_rat_denseUpcrossings_lt_top
    (fun t ↦ hX.integral_norm_le_endpoints (min_le_right t (N : ℝ≥0)))

theorem Supermartingale.ae_all_rat_denseUpcrossings_neg_min_lt_top
    (hX : Supermartingale X F P) :
    ∀ᵐ ω ∂P, ∀ N : ℕ, ∀ a b : ℚ, a < b →
      denseUpcrossings a b (fun t ω ↦ -X (min t (N : ℝ≥0)) ω) ω < ⊤ :=
  hX.neg.ae_all_rat_denseUpcrossings_min_lt_top

end MeasureTheory
