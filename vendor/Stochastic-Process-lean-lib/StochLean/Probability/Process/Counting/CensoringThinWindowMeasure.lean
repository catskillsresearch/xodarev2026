/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.Counting.CensoringWindow
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
public import Mathlib.Topology.Instances.ENNReal.Lemmas

/-! # Vanishing measures of thin censoring windows

Restrict the original measure to lifetimes with censoring strictly before
arrival but within a decreasing deterministic width. These events decrease
to the empty set. On their intersection both lifetimes would be finite, so
the width limit would force arrival to precede censoring, a contradiction.
Continuity from above gives an actual zero infimum of the restricted
pushforward masses.

The crude-window triangular error is dominated by one of these actual
pushforwards on the same real arrival window. Real coordinates are used
only after proving that the lifetimes on the event are finite. No density,
rate limit, independence or normalized conditional law is assumed.
-/

@[expose] public section

open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
  {T U : Ω → WithTop ℝ≥0}

/-- The actual thin-window pushforward masses decrease to zero under a
finite source measure and are each dominated by the original arrival law. -/
theorem censored_thinWindow_measure_iInf_eq_zero_and_le [IsFiniteMeasure P]
    (hT : Measurable T) (hU : Measurable U) {δ : ℕ → ℝ≥0}
    (hd : Antitone δ) (hlim : Tendsto δ atTop (𝓝 0)) :
    let φ : Ω → ℝ := fun ω ↦ ((T ω).untopA : ℝ)
    let η : ℕ → Measure ℝ := fun n ↦
      (P.restrict {ω | U ω < T ω ∧ T ω < U ω + (δ n : WithTop ℝ≥0)}).map φ
    (⨅ n : ℕ, η n univ) = 0 ∧ ∀ n, η n ≤ P.map φ := by
  intro φ η
  let : MeasurableAdd₂ (WithTop ℝ≥0) := inferInstanceAs (MeasurableAdd₂ ℝ≥0∞)
  let D : ℕ → Set Ω := fun n ↦
    {ω | U ω < T ω ∧ T ω < U ω + (δ n : WithTop ℝ≥0)}
  have hφ : Measurable φ := NNReal.continuous_coe.measurable.comp hT.untopA
  have hmD (n : ℕ) : MeasurableSet (D n) :=
    (measurableSet_lt hU hT).inter (measurableSet_lt hT (hU.add measurable_const))
  have hanti : Antitone D := by
    intro n m hnm ω hω
    exact ⟨hω.1, hω.2.trans_le
      (add_le_add le_rfl (WithTop.coe_le_coe.mpr (hd hnm)))⟩
  have hempty : (⋂ n : ℕ, D n) = ∅ := by
    apply eq_empty_iff_forall_notMem.mpr
    intro ω hω
    have hw (n : ℕ) : U ω < T ω ∧ T ω < U ω + (δ n : WithTop ℝ≥0) :=
      mem_iInter.mp hω n
    have hfin : T ω ≠ ⊤ ∧ U ω ≠ ⊤ :=
      ⟨ne_top_of_lt (hw 0).2, ne_top_of_lt (hw 0).1⟩
    let a := (T ω).untopA
    let b := (U ω).untopA
    have ha : (a : WithTop ℝ≥0) = T ω := by
      dsimp only [a]
      rw [WithTop.untopA_eq_untop hfin.1, WithTop.coe_untop]
    have hb : (b : WithTop ℝ≥0) = U ω := by
      dsimp only [b]
      rw [WithTop.untopA_eq_untop hfin.2, WithTop.coe_untop]
    have hba : b < a := WithTop.coe_lt_coe.mp (by rw [ha, hb]; exact (hw 0).1)
    have hbound (n : ℕ) : a ≤ b + δ n := by
      apply le_of_lt
      apply WithTop.coe_lt_coe.mp
      rw [WithTop.coe_add, ha, hb]
      exact (hw n).2
    have hblim : Tendsto (fun n : ℕ ↦ b + δ n) atTop (𝓝 b) := by
      simpa only [add_zero] using tendsto_const_nhds.add hlim
    exact (not_le_of_gt hba) (ge_of_tendsto' hblim hbound)
  have hmass (n : ℕ) : η n univ = P (D n) := by
    change ((P.restrict (D n)).map φ) univ = P (D n)
    rw [Measure.map_apply hφ MeasurableSet.univ, preimage_univ,
      Measure.restrict_apply_univ]
  constructor
  · simp_rw [hmass]
    rw [← hanti.measure_iInter (fun n ↦ (hmD n).nullMeasurableSet)
      ⟨0, measure_ne_top P (D 0)⟩, hempty, measure_empty]
  · intro n
    exact Measure.map_mono Measure.restrict_le_self hφ

/-- A crude-window censoring error is bounded by the actual thin-window
pushforward on the real arrival interval. Only arrival measurability is
needed for this measure inequality; the source measure may be infinite. -/
theorem censored_wedge_measure_le_thinWindow (hT : Measurable T)
    (ε t h : ℝ≥0) (hh : h ≤ ε) :
    P {ω | (t : WithTop ℝ≥0) ≤ U ω ∧ U ω < T ω ∧
        T ω < ((t + h : ℝ≥0) : WithTop ℝ≥0)} ≤
      ((P.restrict {ω | U ω < T ω ∧ T ω < U ω + (ε : WithTop ℝ≥0)}).map
        (fun ω ↦ ((T ω).untopA : ℝ))) (Ico (t : ℝ) ((t + h : ℝ≥0) : ℝ)) := by
  let φ : Ω → ℝ := fun ω ↦ ((T ω).untopA : ℝ)
  have hφ : Measurable φ := NNReal.continuous_coe.measurable.comp hT.untopA
  change P _ ≤ ((P.restrict _).map φ) _
  rw [Measure.map_apply hφ measurableSet_Ico,
    Measure.restrict_apply (hφ measurableSet_Ico)]
  apply measure_mono
  intro ω hω
  have hfin : T ω ≠ ⊤ ∧ U ω ≠ ⊤ :=
    ⟨ne_top_of_lt hω.2.2, ne_top_of_lt hω.2.1⟩
  let a := (T ω).untopA
  have ha : (a : WithTop ℝ≥0) = T ω := by
    dsimp only [a]
    rw [WithTop.untopA_eq_untop hfin.1, WithTop.coe_untop]
  have hta : t ≤ a := WithTop.coe_le_coe.mp (by
    rw [ha]
    exact hω.1.trans hω.2.1.le)
  have hat : a < t + h := WithTop.coe_lt_coe.mp (by rw [ha]; exact hω.2.2)
  refine ⟨⟨?_, ?_⟩, hω.2.1, hω.2.2.trans_le ?_⟩
  · change (t : ℝ) ≤ (a : ℝ)
    exact_mod_cast hta
  · change (a : ℝ) < ((t + h : ℝ≥0) : ℝ)
    exact_mod_cast hat
  · rw [WithTop.coe_add]
    exact add_le_add hω.1 (WithTop.coe_le_coe.mpr hh)

end ProbabilityTheory
