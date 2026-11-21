/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.TimeChange.InverseClockProcess
public import StochLean.Probability.Process.Semimartingale.QuadraticVariation.ContinuousConstancyIntervals

/-! # The nonnegative-real view of the existing continuous quadratic variation

This is only a codomain conversion of the canonical continuous bracket, not
a new quadratic-variation construction. Its real value is exactly the same
bracket everywhere. Continuous local martingales are constant on its fibers
on a single common event, without an initial-moment assumption.
-/

@[expose] public section

open MeasureTheory Filter Set
open scoped NNReal

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsFiniteMeasure P]
  {F : Filtration ℝ≥0 mΩ} {X : ℝ≥0 → Ω → ℝ}

noncomputable def IsSemimartingale.continuousBracketClock
    (hX : IsSemimartingale X F P) (hF : F.IsUsual P) : ℝ≥0 → Ω → ℝ≥0 :=
  fun t ω ↦ (hX.continuousQuadraticVariation hF t ω).toNNReal

theorem IsSemimartingale.coe_continuousBracketClock
    (hX : IsSemimartingale X F P) (hF : F.IsUsual P) (t : ℝ≥0) (ω : Ω) :
    (hX.continuousBracketClock hF t ω : ℝ) = hX.continuousQuadraticVariation hF t ω :=
  Real.coe_toNNReal _ (hX.continuousQuadraticVariation_nonneg hF t ω)

theorem IsSemimartingale.adapted_continuousBracketClock
    (hX : IsSemimartingale X F P) (hF : F.IsUsual P) :
    Adapted F (hX.continuousBracketClock hF) := fun t ↦
  continuous_real_toNNReal.measurable.comp (hX.adapted_continuousQuadraticVariation hF t)

theorem IsSemimartingale.continuous_continuousBracketClock
    (hX : IsSemimartingale X F P) (hF : F.IsUsual P) (ω : Ω) :
    Continuous (fun t ↦ hX.continuousBracketClock hF t ω) :=
  continuous_real_toNNReal.comp (hX.continuous_continuousQuadraticVariation hF ω)

theorem IsSemimartingale.monotone_continuousBracketClock
    (hX : IsSemimartingale X F P) (hF : F.IsUsual P) (ω : Ω) :
    Monotone (fun t ↦ hX.continuousBracketClock hF t ω) :=
  Real.toNNReal_monotone.comp (hX.monotone_continuousQuadraticVariation hF ω)

theorem IsSemimartingale.continuousBracketClock_zero
    (hX : IsSemimartingale X F P) (hF : F.IsUsual P) (ω : Ω) :
    hX.continuousBracketClock hF 0 ω = 0 := by
  apply NNReal.coe_injective
  rw [hX.coe_continuousBracketClock hF, hX.continuousQuadraticVariation_zero hF, NNReal.coe_zero]

theorem IsSemimartingale.continuousBracketClock_unbounded_of_tendsto
    (hX : IsSemimartingale X F P) (hF : F.IsUsual P)
    (hu : ∀ᵐ ω ∂P, Tendsto (hX.continuousQuadraticVariation hF · ω) atTop atTop) :
    ∀ᵐ ω ∂P, ∀ s : ℝ≥0, ∃ t, s < hX.continuousBracketClock hF t ω := by
  filter_upwards [hu] with ω hω s
  obtain ⟨t, ht⟩ := (hω.eventually (eventually_gt_atTop (s : ℝ))).exists
  refine ⟨t, ?_⟩
  change (s : ℝ) < (hX.continuousBracketClock hF t ω : ℝ)
  rwa [hX.coe_continuousBracketClock hF]

theorem IsContinuousLocalMartingale.ae_eq_of_continuousBracketClock_eq
    (hX : IsContinuousLocalMartingale X F P) (hF : F.IsUsual P) :
    ∀ᵐ ω ∂P, ∀ s t, (hX.isSemimartingale hF).continuousBracketClock hF s ω =
      (hX.isSemimartingale hF).continuousBracketClock hF t ω → X s ω = X t ω := by
  filter_upwards [hX.ae_continuousQuadraticVariation_eq_iff_eqOn_Icc hF] with ω he
  have hpair (s t : ℝ≥0) (hst : s ≤ t)
      (h : (hX.isSemimartingale hF).continuousBracketClock hF s ω =
        (hX.isSemimartingale hF).continuousBracketClock hF t ω) : X s ω = X t ω := by
    have hq := congrArg (fun a : ℝ≥0 ↦ (a : ℝ)) h
    rw [(hX.isSemimartingale hF).coe_continuousBracketClock hF,
      (hX.isSemimartingale hF).coe_continuousBracketClock hF] at hq
    exact (((he s t hst).mp hq) ⟨hst, le_rfl⟩).symm
  intro s t h
  rcases le_total s t with hst | hts
  · exact hpair s t hst h
  · exact (hpair t s hts h.symm).symm

end ProbabilityTheory
