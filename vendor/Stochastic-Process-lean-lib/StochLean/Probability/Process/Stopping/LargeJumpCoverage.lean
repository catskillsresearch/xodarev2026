/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.Stopping.LargeJumpSequence
public import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-! # Measurable finite-prefix coverage of actual large jumps

The good event is that the first omitted entry in the existing large-jump
sequence is beyond the compact horizon. Local finiteness of cadlag jumps
already proves pointwise escape, and bounded indicator convergence makes the
probability of its complement tend to zero. No jump-count moment is assumed.

On the good event the prefix `range K` covers all positive-time strict large
jumps up to the horizon. Finite indexed lifetimes are distinct, while repeated
infinity remains permitted. These are the actual coverage and uniqueness
inputs required by finite jump removal.
-/

@[expose] public section

open MeasureTheory Filter Set
open scoped NNReal Topology

namespace MeasureTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {F : Filtration ℝ≥0 mΩ}
  {P : Measure Ω} [IsFiniteMeasure P]

theorem tendsto_measureReal_stoppingTime_le_of_ae_eventually_gt
    {σ : ℕ → Ω → WithTop ℝ≥0} (hσ : ∀ n, IsStoppingTime F (σ n))
    (T : ℝ≥0) (hdiv : ∀ᵐ ω ∂P, ∀ᶠ n in atTop, (T : WithTop ℝ≥0) < σ n ω) :
    Tendsto (fun n ↦ P.real {ω | σ n ω ≤ (T : WithTop ℝ≥0)}) atTop (𝓝 0) := by
  have hm (n : ℕ) : MeasurableSet {ω | σ n ω ≤ (T : WithTop ℝ≥0)} :=
    F.le T _ (hσ n T)
  have hlim : ∀ᵐ ω ∂P, Tendsto
      (fun n ↦ {ω | σ n ω ≤ (T : WithTop ℝ≥0)}.indicator (fun _ ↦ (1 : ℝ)) ω)
      atTop (𝓝 (0 : ℝ)) := by
    filter_upwards [hdiv] with ω hω
    apply tendsto_const_nhds.congr'
    filter_upwards [hω] with n hn
    exact (indicator_of_notMem (not_le_of_gt hn) (fun _ ↦ (1 : ℝ))).symm
  have hint := tendsto_integral_of_dominated_convergence (fun _ : Ω ↦ (1 : ℝ))
    (fun n ↦ (measurable_const.indicator (hm n)).aestronglyMeasurable)
    (integrable_const (1 : ℝ))
    (fun n ↦ Eventually.of_forall fun ω ↦
      (norm_indicator_le_norm_self (fun _ : Ω ↦ (1 : ℝ)) ω).trans_eq (norm_one (α := ℝ)))
    hlim
  simpa only [integral_indicator (hm _), integral_const, Measure.real,
    Measure.restrict_apply_univ, smul_eq_mul, mul_one, mul_zero] using hint

end MeasureTheory

namespace ProbabilityTheory

variable {Ω : Type*}

/-- The first omitted actual large-jump lifetime is beyond the horizon. -/
noncomputable def largeJumpCoverageEvent (X : ℝ≥0 → Ω → ℝ) (b : ℝ)
    (T : ℝ≥0) (K : ℕ) : Set Ω :=
  {ω | (T : WithTop ℝ≥0) < largeJumpSequence X b K ω}

theorem monotone_largeJumpCoverageEvent (X : ℝ≥0 → Ω → ℝ) (b : ℝ) (T : ℝ≥0) :
    Monotone (largeJumpCoverageEvent X b T) := by
  intro K L hKL ω hω
  exact hω.trans_le (monotone_largeJumpSequence X b ω hKL)

theorem largeJumpCoverageEvent_compl (X : ℝ≥0 → Ω → ℝ) (b : ℝ) (T : ℝ≥0) (K : ℕ) :
    (largeJumpCoverageEvent X b T K)ᶜ =
      {ω | largeJumpSequence X b K ω ≤ (T : WithTop ℝ≥0)} := by
  ext ω
  simp only [largeJumpCoverageEvent, mem_compl_iff, mem_ofPred_eq, not_lt]

theorem IsCadlagPath.largeJumpSequence_prefix_distinct
    {X : ℝ≥0 → Ω → ℝ} {ω : Ω} (hX : IsCadlagPath (X · ω))
    {b : ℝ} (hb : 0 < b) (K : ℕ) :
    ∀ i ∈ Finset.range K, ∀ j ∈ Finset.range K, ∀ t : ℝ≥0,
      largeJumpSequence X b i ω = (t : WithTop ℝ≥0) →
      largeJumpSequence X b j ω = (t : WithTop ℝ≥0) → i = j := by
  intro i _ j _ t hit hjt
  have hfin : largeJumpSequence X b j ω ≠ ⊤ :=
    fun htop ↦ WithTop.coe_ne_top (hjt.symm.trans htop)
  exact (hX.largeJumpSequence_eq_iff_of_ne_top hb hfin).mp (hit.trans hjt.symm)

theorem IsCadlagPath.largeJumpSequence_prefix_covers_on_coverageEvent
    {X : ℝ≥0 → Ω → ℝ} {ω : Ω} (hX : IsCadlagPath (X · ω))
    {b : ℝ} (hb : 0 < b) {T : ℝ≥0} {K : ℕ}
    (hgood : ω ∈ largeJumpCoverageEvent X b T K) :
    ∀ t : ℝ≥0, 0 < t → t ≤ T → b < ‖jumpProcess X t ω‖ →
      ∃ i ∈ Finset.range K, largeJumpSequence X b i ω = (t : WithTop ℝ≥0) := by
  intro t ht htT hj
  obtain ⟨i, hi, hit⟩ := hX.largeJumpSequence_covers_Ioc_of_lt hb hgood t ht htT hj
  exact ⟨i, Finset.mem_range.mpr hi, hit⟩

end ProbabilityTheory

namespace MeasureTheory

open ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {F : Filtration ℝ≥0 mΩ}
  {X : ℝ≥0 → Ω → ℝ} {b : ℝ}

theorem Adapted.measurableSet_largeJumpCoverageEvent [F.IsRightContinuous]
    (hX : Adapted F X) (hc : ∀ ω, IsCadlagPath (X · ω)) (hb : 0 < b)
    (T : ℝ≥0) (K : ℕ) : MeasurableSet[F T] (largeJumpCoverageEvent X b T K) :=
  (hX.isStoppingTime_largeJumpSequence hc hb K).measurableSet_gt T

theorem Adapted.tendsto_measureReal_largeJumpSequence_le
    {P : Measure Ω} [IsFiniteMeasure P] [F.IsRightContinuous]
    (hX : Adapted F X) (hc : ∀ ω, IsCadlagPath (X · ω)) (hb : 0 < b)
    (T : ℝ≥0) :
    Tendsto (fun K ↦ P.real {ω | largeJumpSequence X b K ω ≤ (T : WithTop ℝ≥0)})
      atTop (𝓝 0) :=
  tendsto_measureReal_stoppingTime_le_of_ae_eventually_gt
    (hX.isStoppingTime_largeJumpSequence hc hb) T
    (Eventually.of_forall fun ω ↦ (hc ω).eventually_gt_largeJumpSequence hb T)

theorem Adapted.tendsto_measureReal_largeJumpCoverageEvent_compl
    {P : Measure Ω} [IsFiniteMeasure P] [F.IsRightContinuous]
    (hX : Adapted F X) (hc : ∀ ω, IsCadlagPath (X · ω)) (hb : 0 < b)
    (T : ℝ≥0) :
    Tendsto (fun K ↦ P.real (largeJumpCoverageEvent X b T K)ᶜ) atTop (𝓝 0) := by
  simpa only [largeJumpCoverageEvent_compl] using
    hX.tendsto_measureReal_largeJumpSequence_le (P := P) hc hb T

end MeasureTheory
