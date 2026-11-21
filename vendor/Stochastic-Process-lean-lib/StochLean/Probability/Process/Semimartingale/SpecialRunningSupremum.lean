/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.Semimartingale.SpecialIntegrableVariation
public import StochLean.Probability.Process.LocalMartingale.RunningSupremum
public import StochLean.Probability.Process.Path.RunningJumpSupremumStopping
public import StochLean.Probability.Process.Measurability.RunningJumpSupremum

/-! # Locally integrable running suprema of special semimartingales

The actual canonical local martingale supplies a whole-path integrable
envelope after native localization. Its localizing sequence is intersected
with a sequence making the actual canonical FV part integrable in variation.
That part starts at zero almost surely, so its stopped variation supplies
the remaining envelope without any moment assumption on the original initial
value.

The resulting envelope controls the original running norm supremum and the
actual all-times running jump supremum, stopped with the same native masks.
The jump bound retains the factor two and the initial jump. The extended
suprema are genuinely finite on the common good event before conversion to
real values. Neither an alternative supremum nor a localizer is defined here.
-/

@[expose] public section

open MeasureTheory Filter Set
open scoped NNReal ENNReal

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
  {F : Filtration ℝ≥0 mΩ} {X : ℝ≥0 → Ω → ℝ} [IsProbabilityMeasure P]

/-- An actual special decomposition provides native localizations with
integrable whole-half-line envelopes, even for a nonintegrable initial value. -/
theorem IsSpecialSemimartingale.locally_integrable_envelope
    (hX : IsSpecialSemimartingale X F P) (hF : F.IsUsual P) :
    Locally (fun Y ↦ ∃ G : Ω → ℝ, Integrable G P ∧
      ∀ᵐ ω ∂P, ∀ t, ‖Y t ω‖ ≤ G ω) F X P := by
  let M := hX.canonicalMartingalePart
  let A := hX.canonicalFiniteVariationPart
  obtain ⟨hM, _, _, _, _, hA0, he⟩ := hX.canonicalDecomposition_properties hF
  obtain ⟨τ, hτ, hG⟩ := hM.locally_integrable_envelope hF
  obtain ⟨σ, hσ, hvσ⟩ := hasLocallyIntegrableVariation_iff_exists_stopped.mp
    (hX.canonicalFiniteVariationPart_hasLocallyIntegrableVariation hF)
  let ρ := min τ σ
  have hρ : IsLocalizingSequence F ρ P := hτ.min hσ
  refine ⟨ρ, hρ, fun n ↦ ?_⟩
  obtain ⟨G, hiG, hbG⟩ := hG n
  change ∀ᵐ ω ∂P, ∀ t, ‖MeasureTheory.stoppedProcess
    (fun s ↦ {v | 0 < τ n v}.indicator (M s)) (τ n) t ω‖ ≤ G ω at hbG
  let V : Ω → ℝ := fun ω ↦
    (eVariationOn (fun t ↦ MeasureTheory.stoppedProcess A (σ n) t ω) univ).toReal
  have hiV : Integrable V P := (hvσ n).integrable_eVariationOn_toReal
  refine ⟨fun ω ↦ G ω + V ω, hiG.add hiV, ?_⟩
  filter_upwards [hbG, (hvσ n).ae_forall_norm_sub_le, hA0, he] with ω hGω hVω hAω heω t
  change ‖MeasureTheory.stoppedProcess
    (fun s ↦ {ω | 0 < ρ n ω}.indicator (X s)) (ρ n) t ω‖ ≤ G ω + V ω
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
    have hMu : ‖M u ω‖ ≤ G ω := by
      simpa only [stoppedProcess_eq_of_le huτ, indicator_of_mem hmemτ] using hGω u
    have ha0 : MeasureTheory.stoppedProcess A (σ n) 0 ω = 0 := by
      rw [stoppedProcess_eq_of_le (i := (0 : ℝ≥0)) bot_le]
      exact hAω
    have hAu : ‖A u ω‖ ≤ V ω := by
      have h := hVω 0 u
      change ‖MeasureTheory.stoppedProcess A (σ n) u ω -
        MeasureTheory.stoppedProcess A (σ n) 0 ω‖ ≤ V ω at h
      simpa only [stoppedProcess_eq_of_le huσ, ha0, sub_zero] using h
    change ‖X u ω‖ ≤ G ω + V ω
    have heu : X u ω = M u ω + A u ω := heω u
    rw [heu]
    exact (norm_add_le _ _).trans (add_le_add hMu hAu)
  · rw [indicator_of_notMem (show ω ∉ {v | 0 < ρ n v} from hp), norm_zero]
    have hG0 : 0 ≤ G ω := (norm_nonneg _).trans (hGω 0)
    exact add_nonneg hG0 ENNReal.toReal_nonneg

/-- The original running norm supremum is locally integrable in the native
masked sense. The assertion concerns its actual stopped process, not merely
running suprema of unrelated local versions. -/
theorem IsSpecialSemimartingale.locally_integrable_denseRunningSupremum
    (hX : IsSpecialSemimartingale X F P) (hF : F.IsUsual P) :
    Locally (fun Y ↦ ∀ t, Integrable (Y t) P) F
      (fun t ω ↦ (denseRunningSupremum (fun s v ↦ ‖X s v‖) t ω).toReal) P := by
  obtain ⟨τ, hτ, hG⟩ := hX.locally_integrable_envelope hF
  refine ⟨τ, hτ, fun n T ↦ ?_⟩
  obtain ⟨G, hiG, hb⟩ := hG n
  let Y := MeasureTheory.stoppedProcess (fun t ↦ {ω | 0 < τ n ω}.indicator (X t)) (τ n)
  change ∀ᵐ ω ∂P, ∀ t, ‖Y t ω‖ ≤ G ω at hb
  have hcMask := hX.2.1.indicator {ω | 0 < τ n ω}
  have haMask : Adapted F (fun t ↦ {ω | 0 < τ n ω}.indicator (X t)) :=
    hX.1.indicator_initial ((hτ.isStoppingTime n).measurableSet_gt 0)
  have haY : Adapted F Y :=
    (haMask.stronglyAdapted.stoppedProcess_of_usual hF hcMask.hasRightContinuousPaths
      (hτ.isStoppingTime n)).adapted
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
  filter_upwards [hX.2.1] with ω hω
  exact denseRunningSupremum_norm_masked_stoppedProcess hω.1 (τ n) T

/-- The actual all-times running jump supremum, including the initial jump,
is locally integrable with native masks. The controlling path bound has
factor two; a dense grid is never substituted for the actual jump times. -/
theorem IsSpecialSemimartingale.locally_integrable_runningJumpSupremum
    (hX : IsSpecialSemimartingale X F P) (hF : F.IsUsual P) :
    Locally (fun Y ↦ ∀ t, Integrable (Y t) P) F
      (fun t ω ↦ (eRunningJumpSupremum X t ω).toReal) P := by
  obtain ⟨τ, hτ, hG⟩ := hX.locally_integrable_envelope hF
  refine ⟨τ, hτ, fun n T ↦ ?_⟩
  obtain ⟨G, hiG, hb⟩ := hG n
  let Y := MeasureTheory.stoppedProcess (fun t ↦ {ω | 0 < τ n ω}.indicator (X t)) (τ n)
  change ∀ᵐ ω ∂P, ∀ t, ‖Y t ω‖ ≤ G ω at hb
  have hcMask := hX.2.1.indicator {ω | 0 < τ n ω}
  have hcY : HasCadlagPaths Y P := hcMask.stoppedProcess (τ n)
  have haMask : Adapted F (fun t ↦ {ω | 0 < τ n ω}.indicator (X t)) :=
    hX.1.indicator_initial ((hτ.isStoppingTime n).measurableSet_gt 0)
  have haY : Adapted F Y :=
    (haMask.stronglyAdapted.stoppedProcess_of_usual hF hcMask.hasRightContinuousPaths
      (hτ.isStoppingTime n)).adapted
  have hm : Measurable (eRunningJumpSupremum Y T) :=
    ((haY.eRunningJumpSupremum_of_usual hF hcY) T).mono (F.le T) le_rfl
  have hi : Integrable (fun ω ↦ (eRunningJumpSupremum Y T ω).toReal) P := by
    apply (hiG.const_mul 2).mono' hm.ennreal_toReal.aestronglyMeasurable
    filter_upwards [hb, hcY] with ω hω hcω
    rw [Real.norm_of_nonneg ENNReal.toReal_nonneg]
    have hG0 : 0 ≤ G ω := (norm_nonneg (Y 0 ω)).trans (hω 0)
    have hbound : eRunningJumpSupremum Y T ω ≤ ENNReal.ofReal (2 * G ω) := by
      calc
        _ ≤ 2 * denseRunningSupremum (fun t v ↦ ‖Y t v‖) T ω :=
          hcω.eRunningJumpSupremum_le_two_mul T
        _ ≤ 2 * ENNReal.ofReal (G ω) :=
          mul_le_mul' le_rfl (denseRunningSupremum_le_of_le (fun t _ ↦ hω t))
        _ = _ := by
          rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2), ENNReal.ofReal_ofNat]
    have ht := (ENNReal.toReal_le_toReal
      (hcω.eRunningJumpSupremum_ne_top T) ENNReal.ofReal_ne_top).mpr hbound
    simpa only [ENNReal.toReal_ofReal (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hG0)] using ht
  apply hi.congr
  filter_upwards [hX.2.1] with ω hω
  exact hω.eRunningJumpSupremum_toReal_masked_stoppedProcess (τ n) T

end ProbabilityTheory
