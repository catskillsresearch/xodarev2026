/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.LocalMartingale.FundamentalDecomposition
public import StochLean.Probability.Process.Path.RightContinuousSupremum

/-! # Locally integrable running suprema of local martingales

The actual fundamental decomposition and bounded-jump localization provide
an integrable whole-path envelope for native masked stopped local martingales.
The finite-variation part starts at zero, so its actual stopped total variation
is the second term of the envelope. No initial moment is required for the
original process: the existing positive-lifetime mask is retained.

The second conclusion concerns the original running norm supremum process,
using only `denseRunningSupremum`. A path identity commutes this supremum with
masked stopping, with separate zero and infinite lifetime cases. Its extended
value is proved finite before converting to a real value and proving L1.
This does not assert local unmasked integrability of an arbitrary initial
random value; the source zero-initial convention is generalized by native
masked localization, not by discarding the initial value.
-/

@[expose] public section

open MeasureTheory Filter Set
open scoped NNReal ENNReal

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
  {F : Filtration ℝ≥0 mΩ} {M : ℝ≥0 → Ω → ℝ}

private theorem denseRunningSupremum_min_const {X : ℝ≥0 → Ω → ℝ} {ω : Ω}
    (hX : IsRightContinuousPath (X · ω)) (T a : ℝ≥0) :
    denseRunningSupremum (fun t ↦ X (min t a)) T ω =
      denseRunningSupremum X (min T a) ω := by
  apply le_antisymm
  · apply iSup_le
    intro n
    exact ofReal_le_denseRunningSupremum_of_rightContinuous
      (le_min ((min_le_left _ _).trans (min_le_left _ _)) (min_le_right _ _)) hX
  · apply iSup_le
    intro n
    have huT : denseTimeUpTo (min T a) n ≤ T :=
      (min_le_left _ _).trans (min_le_left _ _)
    have hua : denseTimeUpTo (min T a) n ≤ a :=
      (min_le_left _ _).trans (min_le_right _ _)
    simpa only [min_eq_left hua] using
      (ofReal_le_denseRunningSupremum_of_rightContinuous
        (X := fun t ↦ X (min t a)) huT (hX.min_const a))

/-- The existing running norm supremum commutes with native masked stopping
on every right-continuous path, including zero and infinite lifetimes. -/
theorem denseRunningSupremum_norm_masked_stoppedProcess
    {X : ℝ≥0 → Ω → ℝ} {ω : Ω} (hX : IsRightContinuousPath (X · ω))
    (τ : Ω → WithTop ℝ≥0) (T : ℝ≥0) :
    (denseRunningSupremum (fun t v ↦ ‖MeasureTheory.stoppedProcess
      (fun s ↦ {v | 0 < τ v}.indicator (X s)) τ t v‖) T ω).toReal =
      MeasureTheory.stoppedProcess (fun t ↦ {v | 0 < τ v}.indicator
        (fun v ↦ (denseRunningSupremum (fun s w ↦ ‖X s w‖) t v).toReal)) τ T ω := by
  have hn : IsRightContinuousPath (fun t ↦ ‖X t ω‖) :=
    fun t ↦ continuous_norm.continuousAt.comp_continuousWithinAt (hX t)
  cases hτ : τ ω with
  | top =>
    have hmem : ω ∈ {v | 0 < τ v} := by
      rw [Set.mem_ofPred_eq, hτ]
      exact WithTop.coe_lt_top (0 : ℝ≥0)
    simp only [denseRunningSupremum, MeasureTheory.stoppedProcess, hτ, min_eq_left le_top,
      WithTop.untopA, WithTop.untopD_coe, indicator_of_mem hmem]
  | coe a =>
    by_cases ha : 0 < a
    · have hmem : ω ∈ {v | 0 < τ v} := by
        rw [Set.mem_ofPred_eq, hτ]
        exact WithTop.coe_lt_coe.mpr ha
      have he := congrArg ENNReal.toReal
        (denseRunningSupremum_min_const (X := fun t v ↦ ‖X t v‖) hn T a)
      simpa only [denseRunningSupremum, MeasureTheory.stoppedProcess, hτ,
        ← WithTop.coe_min, WithTop.untopA, WithTop.untopD_coe, indicator_of_mem hmem] using he
    · have hnot : ω ∉ {v | 0 < τ v} := by
        intro hmem
        change 0 < τ ω at hmem
        rw [hτ] at hmem
        exact ha (WithTop.coe_lt_coe.mp hmem)
      simp only [denseRunningSupremum, MeasureTheory.stoppedProcess,
        indicator_of_notMem hnot, norm_zero, ENNReal.ofReal_zero, iSup_const,
        ENNReal.toReal_zero]

variable [IsProbabilityMeasure P]

/-- A general local martingale has actual native localizations dominated on
the whole half-line by integrable random variables. Arbitrary initial values
are retained inside the positive-lifetime masks of those localizations. -/
theorem IsLocalMartingale.locally_integrable_envelope
    (hM : IsLocalMartingale M F P) (hF : F.IsUsual P) :
    Locally (fun Y ↦ ∃ G : Ω → ℝ, Integrable G P ∧
      ∀ᵐ ω ∂P, ∀ t, ‖Y t ω‖ ≤ G ω) F M P := by
  obtain ⟨N, D, hN, _, hD0, _, hvD, he, hjN, _⟩ :=
    hM.exists_fundamental_decomposition_of_pos hF (β := 1) zero_lt_one
  obtain ⟨τ, hτ, hbN⟩ := hN.exists_bounded_fundamentalSequence_of_jump_bound hF
    (C := 2) (by norm_num) (by simpa only [mul_one] using hjN)
  obtain ⟨σ, hσ, hvσ⟩ := hasLocallyIntegrableVariation_iff_exists_stopped.mp hvD
  let ρ := min τ σ
  have hρ : IsLocalizingSequence F ρ P := hτ.isLocalizingSequence.min hσ
  refine ⟨ρ, hρ, fun n ↦ ?_⟩
  let G : Ω → ℝ := fun ω ↦ 2 * (n : ℝ) + 1 + 2 +
    (eVariationOn (fun t ↦ MeasureTheory.stoppedProcess D (σ n) t ω) univ).toReal
  have hiG : Integrable G P :=
    (integrable_const _).add (hvσ n).integrable_eVariationOn_toReal
  refine ⟨G, hiG, ?_⟩
  filter_upwards [(hbN n).1, (hvσ n).ae_forall_norm_sub_le] with ω hn hd t
  change ‖MeasureTheory.stoppedProcess
    (fun s ↦ {ω | 0 < ρ n ω}.indicator (M s)) (ρ n) t ω‖ ≤ G ω
  rw [stoppedProcess_indicator_comm]
  by_cases hp : 0 < ρ n ω
  · rw [indicator_of_mem (show ω ∈ {v | 0 < ρ n v} from hp)]
    let u : ℝ≥0 := (min (t : WithTop ℝ≥0) (ρ n ω)).untopA
    have hne : min (t : WithTop ℝ≥0) (ρ n ω) ≠ ⊤ :=
      ne_top_of_le_ne_top WithTop.coe_ne_top (min_le_left _ _)
    have huρ : (u : WithTop ℝ≥0) ≤ ρ n ω := by
      dsimp only [u]
      rw [WithTop.untopA_eq_untop hne, WithTop.coe_untop]
      exact min_le_right _ _
    have huτ : (u : WithTop ℝ≥0) ≤ τ n ω := huρ.trans (min_le_left _ _)
    have huσ : (u : WithTop ℝ≥0) ≤ σ n ω := huρ.trans (min_le_right _ _)
    have hmemτ : ω ∈ {v | 0 < τ n v} := hp.trans_le (min_le_left _ _)
    have hNu : ‖N u ω‖ ≤ 2 * (n : ℝ) + 1 + 2 := by
      simpa only [stoppedProcess_eq_of_le huτ, indicator_of_mem hmemτ] using hn u
    have hd0 : MeasureTheory.stoppedProcess D (σ n) 0 ω = 0 := by
      rw [stoppedProcess_eq_of_le (i := (0 : ℝ≥0)) bot_le, hD0, Pi.zero_apply]
    have hDu : ‖D u ω‖ ≤
        (eVariationOn (fun s ↦ MeasureTheory.stoppedProcess D (σ n) s ω) univ).toReal := by
      simpa only [stoppedProcess_eq_of_le huσ, hd0, sub_zero] using hd 0 u
    change ‖M u ω‖ ≤ G ω
    rw [show M u ω = N u ω + D u ω from congrFun (congrFun he u) ω]
    exact (norm_add_le _ _).trans (add_le_add hNu hDu)
  · rw [indicator_of_notMem (show ω ∉ {v | 0 < ρ n v} from hp), norm_zero]
    dsimp only [G]
    positivity

/-- Protter III.38's running norm supremum is locally integrable in the
native masked sense. This is the original supremum process stopped along
an actual localizing sequence, not only a supremum of unrelated versions. -/
theorem IsLocalMartingale.locally_integrable_denseRunningSupremum
    (hM : IsLocalMartingale M F P) (hF : F.IsUsual P) :
    Locally (fun Y ↦ ∀ t, Integrable (Y t) P) F
      (fun t ω ↦ (denseRunningSupremum (fun s v ↦ ‖M s v‖) t ω).toReal) P := by
  obtain ⟨τ, hτ, hG⟩ := hM.locally_integrable_envelope hF
  refine ⟨τ, hτ, fun n T ↦ ?_⟩
  obtain ⟨G, hiG, hb⟩ := hG n
  let Y := MeasureTheory.stoppedProcess (fun t ↦ {ω | 0 < τ n ω}.indicator (M t)) (τ n)
  change ∀ᵐ ω ∂P, ∀ t, ‖Y t ω‖ ≤ G ω at hb
  have haY : Adapted F Y := (hM.masked_stoppedProcess hF (hτ.isStoppingTime n)).1
  have hm : Measurable (denseRunningSupremum (fun t ω ↦ ‖Y t ω‖) T) :=
    measurable_denseRunningSupremum
      (fun t ↦ ((haY t).mono (F.le t) le_rfl).norm) T
  have hfin : ∀ᵐ ω ∂P, denseRunningSupremum (fun t v ↦ ‖Y t v‖) T ω ≠ ∞ :=
    hb.mono fun _ hω ↦ denseRunningSupremum_ne_top_of_le (fun t _ ↦ hω t)
  have hi : Integrable (fun ω ↦
      (denseRunningSupremum (fun t v ↦ ‖Y t v‖) T ω).toReal) P := by
    apply hiG.mono' hm.ennreal_toReal.aestronglyMeasurable
    filter_upwards [hb, hfin] with ω hω hf
    rw [Real.norm_of_nonneg ENNReal.toReal_nonneg]
    have hG0 : 0 ≤ G ω := (norm_nonneg (Y 0 ω)).trans (hω 0)
    have hle : denseRunningSupremum (fun t v ↦ ‖Y t v‖) T ω ≤ ENNReal.ofReal (G ω) :=
      denseRunningSupremum_le_of_le (fun t _ ↦ hω t)
    have ht := (ENNReal.toReal_le_toReal hf ENNReal.ofReal_ne_top).mpr hle
    simpa only [ENNReal.toReal_ofReal hG0] using ht
  apply hi.congr
  filter_upwards [hM.2.1] with ω hω
  exact denseRunningSupremum_norm_masked_stoppedProcess hω.1 (τ n) T

end ProbabilityTheory
