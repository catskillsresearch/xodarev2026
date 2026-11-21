/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.Stopping.AnnouncingStability
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.MeasureTheory.Integral.Indicator
public import Mathlib.MeasureTheory.OuterMeasure.BorelCantelli

/-! # Predictability of an attained countable infimum

The finite infimum must almost surely equal one of the original predictable
times. This hypothesis supplies strictness of the announcing terms; arbitrary
decreasing limits of predictable times are not asserted to be predictable.

A summable-probability diagonal controls all original times simultaneously at
successively more dense thresholds. Countable tail infima make the resulting
sequence increasing. Integer caps announce infinity by finite terms, and initial
completeness repairs the exceptional attainment event without imposing strictness
at a zero target. No predictable-graph converse is used.
-/

@[expose] public section

open MeasureTheory Filter Set TopologicalSpace
open scoped NNReal ENNReal Topology

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {F : Filtration ℝ≥0 mΩ}
  {P : Measure Ω} [IsFiniteMeasure P]

/-- An almost surely attained finite countable infimum of predictable times is
predictable. No attainment is required on the infinite-lifetime event. -/
theorem IsPredictableStoppingTime.iInf_nat_of_ae_attained
    {τ : ℕ → Ω → WithTop ℝ≥0}
    (hτ : ∀ i, IsPredictableStoppingTime F (τ i) P) (hF : F.IsUsual P)
    (hatt : ∀ᵐ ω ∂P, (⨅ i, τ i ω) ≠ ⊤ → ∃ i, τ i ω = ⨅ j, τ j ω) :
    IsPredictableStoppingTime F (fun ω ↦ ⨅ i, τ i ω) P := by
  classical
  let : F.IsRightContinuous := hF.rightContinuous
  choose σ hs hle using fun i ↦ (hτ i).exists_announcing_le
  let T (ω : Ω) : WithTop ℝ≥0 := ⨅ i, τ i ω
  let q : ℕ → WithTop ℝ≥0 := denseSeq (WithTop ℝ≥0)
  let E (i n k : ℕ) : Set Ω := ⋃ j : Fin (n + 1),
    {ω | σ i k ω ≤ q j ∧ q j < τ i ω}
  have hmσ (i k : ℕ) : Measurable (σ i k) :=
    ((hs i).isStoppingTime k).measurable.mono
      ((hs i).isStoppingTime k).measurableSpace_le le_rfl
  have hmτ (i : ℕ) : Measurable (τ i) :=
    (hτ i).1.measurable.mono (hτ i).1.measurableSpace_le le_rfl
  have hmE (i n k : ℕ) : MeasurableSet (E i n k) :=
    MeasurableSet.iUnion fun _ ↦
      (measurableSet_le (hmσ i k) measurable_const).inter
        (measurableSet_lt measurable_const (hmτ i))
  have hlimE (i n : ℕ) : Tendsto (fun k ↦ P (E i n k)) atTop (𝓝 0) := by
    have he : ∀ᵐ ω ∂P, ∀ᶠ k in atTop,
        ω ∈ E i n k ↔ ω ∈ (∅ : Set Ω) := by
      filter_upwards [(hs i).tendsto] with ω hω
      have hj (j : Fin (n + 1)) :
          ∀ᶠ k in atTop, ¬(σ i k ω ≤ q j ∧ q j < τ i ω) := by
        by_cases hq : q j < τ i ω
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
        MeasurableSet.empty (hmE i n) he
  let r : ℝ≥0∞ := 2⁻¹
  have hex (n i : ℕ) : ∃ k, P (E i n k) ≤ r ^ (n + i) := by
    obtain ⟨k, hk⟩ := ENNReal.tendsto_atTop_zero.mp (hlimE i n)
      (r ^ (n + i)) (ENNReal.pow_pos (by simp [r]) _)
    exact ⟨k, hk k le_rfl⟩
  choose k hk using hex
  let B (n : ℕ) : Set Ω := ⋃ i, E i n (k n i)
  have hB (n : ℕ) : P (B n) ≤ r ^ n * 2 := by
    calc
      _ ≤ ∑' i, P (E i n (k n i)) := measure_iUnion_le _
      _ ≤ ∑' i, r ^ (n + i) := ENNReal.tsum_le_tsum (hk n)
      _ = r ^ n * 2 := by
        simp only [r, pow_add, ENNReal.tsum_mul_left, ENNReal.tsum_geometric,
          ENNReal.one_sub_inv_two, inv_inv]
  have hsumB : (∑' n, P (B n)) ≠ ∞ := by
    apply ne_top_of_le_ne_top (b := ∑' n, r ^ n * 2) ?_
      (ENNReal.tsum_le_tsum hB)
    simp only [ENNReal.tsum_mul_right, r, ENNReal.tsum_geometric,
      ENNReal.one_sub_inv_two, inv_inv]
    norm_num
  let a (n : ℕ) (ω : Ω) : WithTop ℝ≥0 :=
    Min.min (⨅ i, σ i (k n i) ω) ((n : ℝ≥0) : WithTop ℝ≥0)
  let η (n : ℕ) (ω : Ω) : WithTop ℝ≥0 := ⨅ m ≥ n, a m ω
  have ha (n : ℕ) : IsStoppingTime F (a n) :=
    (IsStoppingTime.iInf fun i ↦ (hs i).isStoppingTime (k n i)).min_const n
  have hη (n : ℕ) : IsStoppingTime F (η n) :=
    IsStoppingTime.biInf (s := Ici n) (Set.to_countable _) (fun m _ ↦ ha m)
  have hηmono (ω : Ω) : Monotone (fun n ↦ η n ω) := by
    intro n m hnm
    exact le_iInf₂ fun j hj ↦ iInf₂_le_of_le j (hnm.trans hj) le_rfl
  have haT (n : ℕ) (ω : Ω) : a n ω ≤ T ω :=
    (min_le_left _ _).trans (iInf_mono fun i ↦ hle i (k n i) ω)
  have hηa (n : ℕ) (ω : Ω) : η n ω ≤ a n ω := iInf₂_le _ le_rfl
  have hηT (n : ℕ) (ω : Ω) : η n ω ≤ T ω := (hηa n ω).trans (haT n ω)
  have hcap : Tendsto (fun n : ℕ ↦ ((n : ℝ≥0) : WithTop ℝ≥0)) atTop (𝓝 ⊤) :=
    WithTop.tendsto_coe_atTop.comp (tendsto_natCast_atTop_atTop (R := ℝ≥0))
  have hηlim : ∀ᵐ ω ∂P, Tendsto (fun n ↦ η n ω) atTop (𝓝 (T ω)) := by
    filter_upwards [ae_eventually_notMem hsumB] with ω hω
    have he : (⨆ n, η n ω) = T ω := by
      apply le_antisymm (iSup_le fun n ↦ hηT n ω)
      apply le_of_forall_lt
      intro x hx
      obtain ⟨y, ⟨j, rfl⟩, hxy, hyT⟩ :=
        (denseRange_denseSeq (WithTop ℝ≥0)).exists_between hx
      have hqtop : q j < ⊤ := hyT.trans_le le_top
      have hevent : ∀ᶠ m in atTop,
          j ≤ m ∧ ω ∉ B m ∧ q j ≤ ((m : ℝ≥0) : WithTop ℝ≥0) := by
        filter_upwards [eventually_ge_atTop j, hω,
          hcap.eventually (Ioi_mem_nhds hqtop)] with m hjm hm hqm
        exact ⟨hjm, hm, hqm.le⟩
      obtain ⟨N, hN⟩ := eventually_atTop.mp hevent
      have hqη : q j ≤ η N ω := by
        apply le_iInf₂
        intro m hm
        obtain ⟨hjm, hωB, hqm⟩ := hN m hm
        apply le_min
        · apply le_iInf
          intro i
          apply le_of_lt
          apply lt_of_not_ge
          intro hσq
          apply hωB
          exact mem_iUnion.mpr ⟨i, mem_iUnion.mpr
            ⟨⟨j, Nat.lt_succ_of_le hjm⟩, hσq, hyT.trans_le (iInf_le _ i)⟩⟩
        · exact hqm
      exact hxy.trans_le (hqη.trans (le_iSup (fun n ↦ η n ω) N))
    rw [← he]
    exact tendsto_atTop_iSup (hηmono ω)
  let G : Set Ω := {ω | T ω ≠ ⊤ → ∃ i, τ i ω = T ω}
  have hGae : ∀ᵐ ω ∂P, ω ∈ G := hatt
  have hG : MeasurableSet[F 0] G := by
    have hGc : MeasurableSet[F 0] Gᶜ := hF.complete_initial _ (ae_iff.mp hGae)
    simpa only [compl_compl] using hGc.compl
  let π (n : ℕ) : Ω → WithTop ℝ≥0 := G.piecewise (η n) (fun _ ↦ 0)
  have hπ (n : ℕ) : IsStoppingTime F (π n) :=
    (hη n).piecewise_of_le (isStoppingTime_const F 0)
      (fun _ ↦ bot_le) (fun _ ↦ bot_le) hG
  refine ⟨IsStoppingTime.iInf (fun i ↦ (hτ i).1), π, hπ,
    fun ω n m hnm ↦ ?_, fun n ω ht ↦ ?_, ?_⟩
  · by_cases hω : ω ∈ G
    · simpa only [π, Set.piecewise, if_pos hω] using hηmono ω hnm
    · simp only [π, Set.piecewise, if_neg hω, le_refl]
  · by_cases hω : ω ∈ G
    · simp only [π, Set.piecewise, if_pos hω]
      change η n ω < T ω
      by_cases hT : T ω = ⊤
      · rw [hT]
        exact ((hηa n ω).trans (min_le_right _ _)).trans_lt (WithTop.coe_lt_top _)
      · obtain ⟨i, hi⟩ := hω hT
        calc
          η n ω ≤ a n ω := hηa n ω
          _ ≤ σ i (k n i) ω := (min_le_left _ _).trans (iInf_le _ i)
          _ < τ i ω := (hs i).strict (k n i) ω (by simpa only [hi] using ht)
          _ = T ω := hi
    · simpa only [π, Set.piecewise, if_neg hω] using ht
  · filter_upwards [hGae, hηlim] with ω hω hl
    simpa only [π, Set.piecewise, if_pos hω] using hl

end ProbabilityTheory
