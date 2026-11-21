/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Martingale.Inequalities.OneSidedWeakCountable
public import StochLean.Probability.Process.Path.RightContinuousSupremum

/-! # Future maximal bounds for nonnegative supermartingales

These are supermartingale estimates, not applications of the opposite-direction
submartingale maximal theorem. The existing signed finite-first-crossing bound
is at most three times the initial mean for a nonnegative supermartingale.
Right continuity transfers its countable-grid bound to a compact interval;
increasing integer horizons and deterministic time shifts give the entire
future half-line. The constant three is explicit and is not claimed sharp.

No usual-filtration assumption, actual supremum finiteness premise, or
evaluation of a never-hit stopping time is required by these interfaces.
-/

@[expose] public section

open ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology

namespace MeasureTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsFiniteMeasure P]
  {F : Filtration ℝ≥0 mΩ} {U : ℝ≥0 → Ω → ℝ}

/-- A compact nonnegative-supermartingale maximal bound, with the explicit
constant inherited from the existing signed first-crossing estimate. -/
theorem Supermartingale.measure_exists_gt_le_three_of_nonneg
    (hU : Supermartingale U F P) (hn : ∀ᵐ ω ∂P, ∀ t, 0 ≤ U t ω)
    (hr : HasRightContinuousPaths U P) (T : ℝ≥0) (a : ℝ≥0) :
    (a : ℝ≥0∞) * P {ω | ∃ t : ℝ≥0, t ≤ T ∧ (a : ℝ) < U t ω} ≤
      ENNReal.ofReal (3 * ∫ ω, U 0 ω ∂P) := by
  have hmean := integral_mono_ae integrable_condExp (hU.integrable 0)
    (hU.condExp_ae_le (show (0 : ℝ≥0) ≤ T from bot_le))
  rw [integral_condExp (F.le 0)] at hmean
  have hnorm : (∫ ω, ‖U T ω‖ ∂P) = ∫ ω, U T ω ∂P :=
    integral_congr_ae (hn.mono fun _ hω ↦ Real.norm_of_nonneg (hω T))
  have hsample := hU.measure_exists_norm_sample_gt_le (denseTimeUpTo T)
    (fun _ ↦ min_le_left _ _) a
  have hbound : (a : ℝ≥0∞) * P {ω | ∃ n, (a : ℝ) < ‖U (denseTimeUpTo T n) ω‖} ≤
      ENNReal.ofReal (3 * ∫ ω, U 0 ω ∂P) := by
    apply hsample.trans
    apply ENNReal.ofReal_le_ofReal
    rw [hnorm]
    linarith
  apply le_trans _ hbound
  apply mul_le_mul le_rfl _ bot_le bot_le
  apply measure_mono_ae
  filter_upwards [hr] with ω hω hcross
  obtain ⟨t, ht, hcross⟩ := hcross
  have hnormcross : (a : ℝ) < ‖U t ω‖ := hcross.trans_le (le_abs_self _)
  exact exists_denseTimeUpTo_exceedance_of_rightContinuous (fun s ↦ (hω s).norm) ht hnormcross

/-- Integer horizons exhaust all finite times. This bound does not presume
that an extended running supremum has a finite real value. -/
theorem Supermartingale.measure_exists_gt_global_le_three_of_nonneg
    (hU : Supermartingale U F P) (hn : ∀ᵐ ω ∂P, ∀ t, 0 ≤ U t ω)
    (hr : HasRightContinuousPaths U P) (a : ℝ≥0) :
    (a : ℝ≥0∞) * P {ω | ∃ t : ℝ≥0, (a : ℝ) < U t ω} ≤
      ENNReal.ofReal (3 * ∫ ω, U 0 ω ∂P) := by
  let E (n : ℕ) := {ω | ∃ t : ℝ≥0, t ≤ (n : ℝ≥0) ∧ (a : ℝ) < U t ω}
  have hm : Monotone E := by
    rintro n m hnm ω ⟨t, ht, ha⟩
    exact ⟨t, ht.trans (Nat.cast_le.mpr hnm), ha⟩
  have he : {ω | ∃ t : ℝ≥0, (a : ℝ) < U t ω} = ⋃ n, E n := by
    ext ω
    simp only [mem_ofPred_eq, mem_iUnion, E]
    constructor
    · rintro ⟨t, ht⟩
      obtain ⟨n, hn⟩ := exists_nat_ge t
      exact ⟨n, t, hn, ht⟩
    · rintro ⟨_, t, _, ht⟩
      exact ⟨t, ht⟩
  rw [he, hm.measure_iUnion, ENNReal.mul_iSup]
  exact iSup_le fun n ↦ hU.measure_exists_gt_le_three_of_nonneg hn hr (n : ℝ≥0) a

/-- Deterministic shifting gives a maximal bound after any starting time.
No stopping-time or usual-filtration hypothesis is inserted by the shift. -/
theorem Supermartingale.measure_exists_future_gt_le_three_of_nonneg
    (hU : Supermartingale U F P) (hn : ∀ᵐ ω ∂P, ∀ t, 0 ≤ U t ω)
    (hr : HasRightContinuousPaths U P) (S : ℝ≥0) (a : ℝ≥0) :
    (a : ℝ≥0∞) * P {ω | ∃ t : ℝ≥0, S ≤ t ∧ (a : ℝ) < U t ω} ≤
      ENNReal.ofReal (3 * ∫ ω, U S ω ∂P) := by
  let e : ℝ≥0 → ℝ≥0 := fun t ↦ S + t
  have he : Monotone e := fun _ _ h ↦ add_le_add le_rfl h
  have hm := hU.reindex e he
  have hn' : ∀ᵐ ω ∂P, ∀ t : ℝ≥0, 0 ≤ U (e t) ω :=
    hn.mono fun _ hω t ↦ hω (e t)
  have hr' : HasRightContinuousPaths (fun t ↦ U (e t)) P := by
    filter_upwards [hr] with ω hω t
    have hc : ContinuousWithinAt e (Ici t) t :=
      (continuous_const.add continuous_id).continuousWithinAt
    apply (hω (e t)).comp hc
    intro r hr
    change S + t ≤ S + r
    change t ≤ r at hr
    exact add_le_add le_rfl hr
  have h := hm.measure_exists_gt_global_le_three_of_nonneg hn' hr' a
  have hset : {ω | ∃ t : ℝ≥0, (a : ℝ) < U (e t) ω} =
      {ω | ∃ t : ℝ≥0, S ≤ t ∧ (a : ℝ) < U t ω} := by
    ext ω
    constructor
    · rintro ⟨t, ht⟩
      exact ⟨e t, le_add_of_nonneg_right (show 0 ≤ t from bot_le), ht⟩
    · rintro ⟨t, hSt, ht⟩
      refine ⟨t - S, ?_⟩
      simpa only [e, add_tsub_cancel_of_le hSt] using ht
  simpa only [hset, e, add_zero] using h

/-- The real-probability version of the future maximal bound. Finiteness of
the underlying measure is explicit before converting the extended measure. -/
theorem Supermartingale.measureReal_exists_future_gt_le_three_of_nonneg
    (hU : Supermartingale U F P) (hn : ∀ᵐ ω ∂P, ∀ t, 0 ≤ U t ω)
    (hr : HasRightContinuousPaths U P) (S : ℝ≥0) {a : ℝ} (ha : 0 < a) :
    P.real {ω | ∃ t : ℝ≥0, S ≤ t ∧ a < U t ω} ≤ (3 * ∫ ω, U S ω ∂P) / a := by
  let a' : ℝ≥0 := ⟨a, ha.le⟩
  have h := hU.measure_exists_future_gt_le_three_of_nonneg hn hr S a'
  have hi : 0 ≤ 3 * ∫ ω, U S ω ∂P := mul_nonneg (by norm_num)
    (integral_nonneg_of_ae (hn.mono fun _ hω ↦ hω S))
  have hreal := ENNReal.toReal_mono ENNReal.ofReal_ne_top h
  have hleft : (a' : ℝ≥0∞).toReal = a := ENNReal.coe_toReal a'
  rw [ENNReal.toReal_mul, hleft, ENNReal.toReal_ofReal hi] at hreal
  apply (le_div_iff₀ ha).mpr
  change a * P.real {ω | ∃ t : ℝ≥0, S ≤ t ∧ a < U t ω} ≤ 3 * ∫ ω, U S ω ∂P at hreal
  nlinarith only [hreal]

end MeasureTheory
