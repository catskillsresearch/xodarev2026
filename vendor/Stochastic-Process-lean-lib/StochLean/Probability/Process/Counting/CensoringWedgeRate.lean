/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.Counting.CensoringThinWindowMeasure
public import StochLean.ForMathlib.MeasureTheory.Measure.RightWindowVanishing
public import Mathlib.Analysis.SpecificLimits.Basic

/-! # The true within-window censoring error has zero rate almost everywhere

The actual triangular event consists of censoring followed strictly by arrival
inside a short observation window. A geometric sequence of genuine thin-window
restricted pushforwards has vanishing total mass, and every one is dominated
by the original real arrival-coordinate law. Absolute continuity therefore
supplies the actual countable RN window bounds.

The proved analytic sandwich theorem makes the true error probability per unit
width vanish almost everywhere in nonnegative time. No independence, continuity
of a joint density, or desired error limit is assumed. This statement does not
claim a pointwise limit at every censoring atom.
-/

@[expose] public section

open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology

namespace ProbabilityTheory

/-- Under absolute continuity of the true real arrival-coordinate law, the
actual probability of censoring before arrival inside a right window, divided
by its width, tends to zero for almost every nonnegative time. -/
theorem ae_tendsto_censored_wedge_rate_zero
    {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsFiniteMeasure P]
    {T U : Ω → WithTop ℝ≥0} (hT : Measurable T) (hU : Measurable U)
    (hAC : P.map (fun ω ↦ ((T ω).untopA : ℝ)) ≪ volume) :
    ∀ᵐ t : ℝ ∂volume, 0 ≤ t →
      Tendsto (fun h : ℝ ↦
        P.real {ω | (t.toNNReal : WithTop ℝ≥0) ≤ U ω ∧ U ω < T ω ∧
          T ω < ((t + h).toNNReal : WithTop ℝ≥0)} / h)
        (𝓝[>] 0) (𝓝 0) := by
  classical
  let δ : ℕ → ℝ≥0 := fun n ↦ (1 / 2 : ℝ≥0) ^ n
  have hd : Antitone δ := fun _ _ h ↦
    pow_le_pow_right_of_le_one' (by norm_num) h
  have hδlim : Tendsto δ atTop (𝓝 0) :=
    NNReal.tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num)
  let φ : Ω → ℝ := fun ω ↦ ((T ω).untopA : ℝ)
  let η : ℕ → Measure ℝ := fun n ↦
    (P.restrict {ω | U ω < T ω ∧ T ω < U ω + (δ n : WithTop ℝ≥0)}).map φ
  have hmass := censored_thinWindow_measure_iInf_eq_zero_and_le
    (P := P) hT hU hd hδlim
  let : ∀ n, IsFiniteMeasure (η n) := fun _ ↦ inferInstance
  have hηAC : ∀ n, η n ≪ volume := fun n ↦
    (Measure.absolutelyContinuous_of_le (hmass.2 n)).trans hAC
  let r : ℝ → ℝ → ℝ := fun t h ↦
    if 0 ≤ t then
      P.real {ω | (t.toNNReal : WithTop ℝ≥0) ≤ U ω ∧ U ω < T ω ∧
        T ω < ((t + h).toNNReal : WithTop ℝ≥0)} / h
    else 0
  have hn : ∀ t, ∀ᶠ h in 𝓝[>] (0 : ℝ), 0 ≤ r t h := by
    intro t
    filter_upwards [self_mem_nhdsWithin] with h hh
    dsimp only [r]
    split_ifs
    · exact div_nonneg measureReal_nonneg hh.le
    · exact le_rfl
  have hb : ∀ n t, ∀ᶠ h in 𝓝[>] (0 : ℝ),
      r t h ≤ (η n).real (Ico t (t + h)) / h := by
    intro n t
    have hδpos : (0 : ℝ) < (δ n : ℝ) := by
      exact_mod_cast (pow_pos (by norm_num : (0 : ℝ≥0) < 1 / 2) n)
    filter_upwards [self_mem_nhdsWithin,
      nhdsWithin_le_nhds (Iio_mem_nhds hδpos)] with h hh hsmall
    by_cases ht : 0 ≤ t
    · have hwidth : h.toNNReal ≤ δ n := Real.toNNReal_le_iff_le_coe.mpr hsmall.le
      have hbound := censored_wedge_measure_le_thinWindow
        (P := P) (U := U) hT (δ n) t.toNNReal h.toNNReal hwidth
      have hmeasure :
          P.real {ω | (t.toNNReal : WithTop ℝ≥0) ≤ U ω ∧ U ω < T ω ∧
            T ω < ((t + h).toNNReal : WithTop ℝ≥0)} ≤
              (η n).real (Ico t (t + h)) := by
        apply (ENNReal.toReal_le_toReal (measure_ne_top P _) (measure_ne_top (η n) _)).mpr
        simpa only [η, φ, Real.toNNReal_add ht hh.le, NNReal.coe_add,
          Real.coe_toNNReal t ht, Real.coe_toNNReal h hh.le] using hbound
      change (if 0 ≤ t then _ else 0) ≤ _
      rw [if_pos ht]
      exact div_le_div_of_nonneg_right hmeasure hh.le
    · change (if 0 ≤ t then _ else 0) ≤ _
      rw [if_neg ht]
      exact div_nonneg measureReal_nonneg hh.le
  have hr := Measure.ae_tendsto_zero_of_eventually_le_measureReal_Ico_div
    η hηAC hmass.1 r hn hb
  filter_upwards [hr] with t ht hnonneg
  simpa only [r, if_pos hnonneg] using ht

end ProbabilityTheory
