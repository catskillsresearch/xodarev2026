/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.Stopping.AnnouncingStability
public import Mathlib.Probability.Process.LocalProperty
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.MeasureTheory.Integral.Indicator
public import Mathlib.MeasureTheory.OuterMeasure.BorelCantelli

/-! # Actual localizers strictly before predictable lifetimes

For every row of announcing times, finitely many integer thresholds detect
failure to have reached a threshold already below the target. Their error
probabilities tend to zero. A summable-probability diagonal and Borel-Cantelli
give selected announcing terms tending almost surely to infinity whenever
the original targets do. No lower growth rate for the targets is assumed.

Integer caps make every selected term finite. Mathlib's actual countable
tail-infimum construction makes the sequence localizing. The resulting
sequence is increasing everywhere, lies below each corresponding original
target everywhere, and is strictly below it whenever that target is positive.
Zero and infinite lifetimes retain the existing announcing conventions.

No diagonal witness, new localizer definition, or predictable-graph converse
is supplied as an extra hypothesis.
-/

@[expose] public section

open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsFiniteMeasure P]
  {F : Filtration ℝ≥0 mΩ} {τ : ℕ → Ω → WithTop ℝ≥0}

/-- A pre-localizing sequence of predictable times admits actual finite,
increasing localizers strictly before every positive corresponding target.
All order and cap conclusions hold everywhere, not merely almost surely. -/
theorem IsPreLocalizingSequence.exists_localizingSequence_lt_of_predictable
    (hτseq : IsPreLocalizingSequence F τ P)
    (hτ : ∀ n, IsPredictableStoppingTime F (τ n) P) (hF : F.IsUsual P) :
    ∃ σ : ℕ → Ω → WithTop ℝ≥0,
      IsLocalizingSequence F σ P ∧ (∀ ω, Monotone (σ · ω)) ∧
      (∀ n ω, σ n ω ≤ τ n ω) ∧
      (∀ n ω, 0 < τ n ω → σ n ω < τ n ω) ∧
      (∀ n ω, σ n ω ≤ ((n : ℝ≥0) : WithTop ℝ≥0)) := by
  classical
  let : F.IsRightContinuous := hF.rightContinuous
  choose a ha hle using fun n ↦ (hτ n).exists_announcing_le
  let q (j : ℕ) : WithTop ℝ≥0 := ((j : ℝ≥0) : WithTop ℝ≥0)
  let E (n k : ℕ) : Set Ω := ⋃ j : Fin (n + 1),
    {ω | a n k ω ≤ q j ∧ q j < τ n ω}
  have hma (n k : ℕ) : Measurable (a n k) :=
    ((ha n).isStoppingTime k).measurable.mono
      ((ha n).isStoppingTime k).measurableSpace_le le_rfl
  have hmτ (n : ℕ) : Measurable (τ n) :=
    (hτseq.isStoppingTime n).measurable.mono
      (hτseq.isStoppingTime n).measurableSpace_le le_rfl
  have hmE (n k : ℕ) : MeasurableSet (E n k) :=
    MeasurableSet.iUnion fun _ ↦
      (measurableSet_le (hma n k) measurable_const).inter
        (measurableSet_lt measurable_const (hmτ n))
  have hlimE (n : ℕ) : Tendsto (fun k ↦ P (E n k)) atTop (𝓝 0) := by
    have he : ∀ᵐ ω ∂P, ∀ᶠ k in atTop,
        ω ∈ E n k ↔ ω ∈ (∅ : Set Ω) := by
      filter_upwards [(ha n).tendsto] with ω hω
      have hj (j : Fin (n + 1)) :
          ∀ᶠ k in atTop, ¬ (a n k ω ≤ q j ∧ q j < τ n ω) := by
        by_cases hq : q j < τ n ω
        · filter_upwards [hω.eventually (Ioi_mem_nhds hq)] with k hk
          exact fun h ↦ (not_le.mpr hk) h.1
        · exact Eventually.of_forall fun _ h ↦ hq h.2
      filter_upwards [eventually_all.mpr hj] with k hk
      simp only [mem_empty_iff_false, iff_false]
      intro hωE
      obtain ⟨j, hj⟩ := mem_iUnion.mp hωE
      exact hk j hj
    simpa only [measure_empty] using
      tendsto_measure_of_ae_tendsto_indicator_of_isFiniteMeasure atTop
        MeasurableSet.empty (hmE n) he
  let r : ℝ≥0∞ := 2⁻¹
  have hex (n : ℕ) : ∃ k, P (E n k) ≤ r ^ n := by
    obtain ⟨k, hk⟩ := ENNReal.tendsto_atTop_zero.mp (hlimE n)
      (r ^ n) (ENNReal.pow_pos (by simp [r]) _)
    exact ⟨k, hk k le_rfl⟩
  choose k hk using hex
  have hsum : (∑' n, P (E n (k n))) ≠ ∞ := by
    apply ne_top_of_le_ne_top (b := ∑' n, r ^ n) ?_ (ENNReal.tsum_le_tsum hk)
    simp only [r, ENNReal.tsum_geometric, ENNReal.one_sub_inv_two, inv_inv]
    norm_num
  let η (n : ℕ) (ω : Ω) : WithTop ℝ≥0 := min (a n (k n) ω) (q n)
  have hη : ∀ n, IsStoppingTime F (η n) :=
    fun n ↦ ((ha n).isStoppingTime (k n)).min_const (n : ℝ≥0)
  have hηlim : ∀ᵐ ω ∂P, Tendsto (η · ω) atTop (𝓝 ⊤) := by
    filter_upwards [ae_eventually_notMem hsum, hτseq.tendsto_top] with ω hω hτω
    apply (WithTop.tendsto_nhds_top_iff _).mpr
    intro t
    obtain ⟨m, htm⟩ := exists_nat_gt t
    have htq : (t : WithTop ℝ≥0) < q m := WithTop.coe_lt_coe.mpr htm
    filter_upwards [eventually_ge_atTop (m + 1), hω,
      hτω.eventually (Ioi_mem_nhds (WithTop.coe_lt_top (m : ℝ≥0)))] with n hmn hn hτn
    have hmle : m ≤ n := (Nat.le_succ m).trans hmn
    have hqa : q m < a n (k n) ω := by
      apply lt_of_not_ge
      intro hleq
      exact hn (mem_iUnion.mpr ⟨⟨m, Nat.lt_succ_of_le hmle⟩, hleq, hτn⟩)
    have hqcap : q m < q n :=
      WithTop.coe_lt_coe.mpr (Nat.cast_lt.mpr (Nat.lt_of_succ_le hmn))
    exact lt_min (htq.trans hqa) (htq.trans hqcap)
  have hηpre : IsPreLocalizingSequence F η P := ⟨hη, hηlim⟩
  let σ (n : ℕ) (ω : Ω) : WithTop ℝ≥0 := ⨅ m ≥ n, η m ω
  have hση (n : ℕ) (ω : Ω) : σ n ω ≤ η n ω := iInf₂_le _ le_rfl
  refine ⟨σ, hηpre.isLocalizingSequence_biInf, ?_, ?_, ?_, ?_⟩
  · intro ω n m hnm
    exact le_iInf₂ fun j hj ↦ iInf₂_le_of_le j (hnm.trans hj) le_rfl
  · intro n ω
    exact ((hση n ω).trans (min_le_left _ _)).trans (hle n (k n) ω)
  · intro n ω ht
    exact ((hση n ω).trans (min_le_left _ _)).trans_lt ((ha n).strict (k n) ω ht)
  · intro n ω
    exact (hση n ω).trans (min_le_right _ _)

end ProbabilityTheory
