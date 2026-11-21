/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.TimeChange.QuadraticVariationClock

/-! # Actual bracket bounds and levels at inverse-clock stopping times

The stopped bound holds even when the inverse time is infinite. The level
identity separately requires divergence of the bracket, so no value at an
infinite stopping time is substituted for a terminal value.
-/

@[expose] public section

open MeasureTheory Filter
open scoped NNReal Topology

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsFiniteMeasure P]
  {F : Filtration ℝ≥0 mΩ} {X : ℝ≥0 → Ω → ℝ}

theorem IsSemimartingale.stopped_continuousQuadraticVariation_inverseClock_le
    (hX : IsSemimartingale X F P) (hF : F.IsUsual P) (s t : ℝ≥0) (ω : Ω) :
    MeasureTheory.stoppedProcess (hX.continuousQuadraticVariation hF)
      (clockInverseTime (hX.continuousBracketClock hF) s) t ω ≤ s := by
  let A := hX.continuousBracketClock hF
  let τ := clockInverseTime A s
  let v := (min (t : WithTop ℝ≥0) (τ ω)).untopA
  have hn : min (t : WithTop ℝ≥0) (τ ω) ≠ ⊤ :=
    ne_top_of_le_ne_top WithTop.coe_ne_top (min_le_left _ _)
  have hv : (v : WithTop ℝ≥0) = min (t : WithTop ℝ≥0) (τ ω) := by
    dsimp only [v]
    rw [WithTop.untopA_eq_untop hn, WithTop.coe_untop]
  have ha : A v ω ≤ s := (le_rightClockInverse_iff
    (hX.continuous_continuousBracketClock hF ω) (hX.monotone_continuousBracketClock hF ω)
    (hX.continuousBracketClock_zero hF ω) s v).mp (by rw [hv]; exact min_le_right _ _)
  change hX.continuousQuadraticVariation hF v ω ≤ (s : ℝ)
  rw [← hX.coe_continuousBracketClock hF v ω]
  exact ha

theorem IsSemimartingale.stoppedValue_continuousQuadraticVariation_inverseClock
    (hX : IsSemimartingale X F P) (hF : F.IsUsual P)
    (hu : ∀ᵐ ω ∂P, Tendsto (hX.continuousQuadraticVariation hF · ω) atTop atTop) :
    Indistinguishable (fun s ↦ stoppedValue (hX.continuousQuadraticVariation hF)
      (clockInverseTime (hX.continuousBracketClock hF) s)) (fun s _ ↦ (s : ℝ)) P := by
  have h := clockInverseTime_value
    (Eventually.of_forall (hX.continuous_continuousBracketClock hF))
    (Eventually.of_forall (hX.monotone_continuousBracketClock hF))
    (Eventually.of_forall (hX.continuousBracketClock_zero hF))
    (hX.continuousBracketClock_unbounded_of_tendsto hF hu)
  filter_upwards [h] with ω hω s
  have he := congrArg (fun x : ℝ≥0 ↦ (x : ℝ)) (hω s)
  change (hX.continuousBracketClock hF
    (clockInverseTime (hX.continuousBracketClock hF) s ω).untopA ω : ℝ) = (s : ℝ) at he
  rw [hX.coe_continuousBracketClock hF] at he
  exact he

end ProbabilityTheory
