/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.FiniteVariation.BoundedJumpLocalization

/-! # Integrable jump envelopes give locally integrable variation

The existing total-variation process is zero-initial, and its positive-time
jump is the norm of the original jump. On each path the deterministic capped
exit estimate accepts the real constant given by an actual random envelope.
This bounds the original stopped whole-half-line variation by the exit level
plus that envelope, including the possibly overshooting exit jump.

The extended variation is measurable and finite before its real conversion
is used for the L1 comparison. No boundedness or integrability is imposed on
the original initial random value. The localizers remain the existing capped
exits of actual total variation; no replacement variation or selector is used.
-/

@[expose] public section

open MeasureTheory StochLean Filter Set
open scoped NNReal ENNReal

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsFiniteMeasure P]
  {F : Filtration ℝ≥0 mΩ} {A : ℝ≥0 → Ω → ℝ} {G : Ω → ℝ}

namespace HasFiniteVariationPaths

/-- The original variation exits give integrable stopped variation when the
positive-time jumps admit a single integrable random envelope. Its AE
nonnegativity follows from the jump bound and is not an extra hypothesis. -/
theorem hasIntegrableVariation_stopped_totalVariation_exit_of_integrable_jump_envelope
    (hv : HasFiniteVariationPaths A P) (ha : Adapted F A) (hF : F.IsUsual P)
    (hc : HasCadlagPaths A P) (hG : Integrable G P)
    (hj : ∀ᵐ ω ∂P, ∀ t : ℝ≥0, 0 < t → ‖jumpProcess A t ω‖ ≤ G ω) (n : ℕ) :
    let ρ := cappedNormExitSequence (totalVariationProcess A) n
    HasIntegrableVariation (MeasureTheory.stoppedProcess A ρ) P ∧
      ∀ᵐ ω ∂P, eVariationOn (fun t ↦ MeasureTheory.stoppedProcess A ρ t ω) univ ≤
        ENNReal.ofReal (((n + 1 : ℕ) : ℝ) + G ω) := by
  let V := totalVariationProcess A
  let ρ := cappedNormExitSequence V n
  let B : Ω → ℝ := fun ω ↦ ((n + 1 : ℕ) : ℝ) + G ω
  have hG0 : ∀ᵐ ω ∂P, 0 ≤ G ω :=
    hj.mono fun ω hω ↦ (norm_nonneg (jumpProcess A 1 ω)).trans (hω 1 zero_lt_one)
  have haV : Adapted F V := ha.totalVariationProcess_of_usual hF hc
  have hcV : HasCadlagPaths V P :=
    hv.hasCadlagPaths_totalVariationProcess hc.hasRightContinuousPaths
  have hV0 : V 0 =ᵐ[P] 0 := Eventually.of_forall fun ω ↦
    congrFun (totalVariationProcess_zero A) ω
  have hjV : ∀ᵐ ω ∂P, ∀ t : ℝ≥0, 0 < t → ‖jumpProcess V t ω‖ ≤ G ω := by
    filter_upwards [hv.ae_jumpProcess_totalVariationProcess hc, hj] with ω he hω t ht
    change ‖jumpProcess (totalVariationProcess A) t ω‖ ≤ G ω
    rw [he t ht, norm_norm]
    exact hω t ht
  have hs : ∀ᵐ ω ∂P, ∀ t, ‖MeasureTheory.stoppedProcess V ρ t ω‖ ≤ B ω := by
    filter_upwards [hcV, hV0, hG0, hjV] with ω hcω h0ω hGω hjω t
    exact hcω.norm_stoppedProcess_cappedNormExitSequence_le_of_jump_bound
      h0ω hGω hjω n t
  have hρ : IsStoppingTime F ρ := haV.isStoppingTime_cappedNormExitSequence hF hcV n
  have hvar : ∀ᵐ ω ∂P, eVariationOn (fun t ↦ MeasureTheory.stoppedProcess A ρ t ω) univ ≤
      ENNReal.ofReal (B ω) := by
    filter_upwards [hv, hs] with ω hvω hω
    have hfin : ρ ω ≠ ⊤ := cappedNormExitSequence_ne_top V n ω
    let r := (ρ ω).untopA
    have hr : (r : WithTop ℝ≥0) = ρ ω := by
      dsimp only [r]
      rw [WithTop.untopA_eq_untop hfin, WithTop.coe_untop]
    have hb : ‖V r ω‖ ≤ B ω := by
      have hsamp := hω r
      rwa [stoppedProcess_eq_of_le hr.le] at hsamp
    have hn : 0 ≤ V r ω := pathTotalVariation_nonneg (A · ω) r
    have hvfin : eVariationOn (A · ω) (Icc 0 r) ≠ ∞ := by
      simpa only [univ_inter, BoundedVariationOn] using hvω 0 r (mem_univ _) (mem_univ _)
    rw [eVariationOn_univ_stoppedProcess, stoppedValueWithTerminal_of_ne_top hfin]
    change eVariationOn (A · ω) (Icc 0 r) ≤ ENNReal.ofReal (B ω)
    rw [← ENNReal.ofReal_toReal hvfin]
    apply ENNReal.ofReal_le_ofReal
    rw [show (eVariationOn (A · ω) (Icc 0 r)).toReal = V r ω from
      (totalVariationProcess_eq_toReal A r ω).symm]
    simpa only [Real.norm_of_nonneg hn] using hb
  have hfin : HasFiniteTotalVariationPaths (MeasureTheory.stoppedProcess A ρ) P :=
    hvar.mono fun _ hω ↦ ne_top_of_le_ne_top ENNReal.ofReal_ne_top hω
  have has := (ha.stronglyAdapted.stoppedProcess_of_usual hF hc.hasRightContinuousPaths hρ).adapted
  have hiB : Integrable B P := (integrable_const _).add hG
  have hi : Integrable (fun ω ↦
      (eVariationOn (fun t ↦ MeasureTheory.stoppedProcess A ρ t ω) univ).toReal) P := by
    apply hiB.mono'
      (has.measurable_eVariationOn_univ_of_usual hF
        (hc.stoppedProcess ρ)).ennreal_toReal.aestronglyMeasurable
    filter_upwards [hvar, hG0] with ω hω hGω
    rw [Real.norm_of_nonneg ENNReal.toReal_nonneg]
    have hB : 0 ≤ B ω := add_nonneg (Nat.cast_nonneg (n + 1)) hGω
    simpa only [ENNReal.toReal_ofReal hB] using
      ENNReal.toReal_mono ENNReal.ofReal_ne_top hω
  exact ⟨⟨hfin, hi⟩, hvar⟩

/-- An actual integrable bound on all positive-time jump norms suffices for
locally integrable variation, without any initial-value moment hypothesis. -/
theorem hasLocallyIntegrableVariation_of_integrable_jump_envelope
    (hv : HasFiniteVariationPaths A P) (ha : Adapted F A) (hF : F.IsUsual P)
    (hc : HasCadlagPaths A P) (hG : Integrable G P)
    (hj : ∀ᵐ ω ∂P, ∀ t : ℝ≥0, 0 < t → ‖jumpProcess A t ω‖ ≤ G ω) :
    HasLocallyIntegrableVariation A F P := by
  have haV := ha.totalVariationProcess_of_usual hF hc
  have hcV := hv.hasCadlagPaths_totalVariationProcess hc.hasRightContinuousPaths
  exact hasLocallyIntegrableVariation_iff_exists_stopped.mpr
    ⟨cappedNormExitSequence (totalVariationProcess A),
      haV.isLocalizingSequence_cappedNormExitSequence hF hcV,
      fun n ↦ (hv.hasIntegrableVariation_stopped_totalVariation_exit_of_integrable_jump_envelope
        ha hF hc hG hj n).1⟩

end HasFiniteVariationPaths
end ProbabilityTheory
