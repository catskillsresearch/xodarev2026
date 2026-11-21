/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.FiniteVariation.JumpEnvelopeLocalization
public import StochLean.Probability.Process.FiniteVariation.LocallyIntegrableLocalization
public import StochLean.Probability.Process.Path.RunningJumpSupremumStopping

/-! # Locally integrable running jumps imply locally integrable variation

The assumed local property is Mathlib's native masked localization of the
actual real running jump supremum, with integrability at every deterministic
time. Intersecting its localizers with positive integer caps produces stopped
finite-variation processes whose jumps admit actual integrable envelopes.

Closed stopping of the running jump supremum identifies each envelope with
the given localized supremum at the cap. Compact cadlag finiteness justifies
the real conversion. Jumps after the cap vanish, while the endpoint is retained.
The existing integrable-jump-envelope theorem and stable native localization
idempotence then yield locally integrable variation of the original process.

No initial moment, extra supremum measurability premise, variation bound,
new running supremum, or new localization predicate is introduced.
-/

@[expose] public section

open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsFiniteMeasure P]
  {F : Filtration ℝ≥0 mΩ} {A : ℝ≥0 → Ω → ℝ}

namespace HasFiniteVariationPaths

/-- Local integrability of the actual running jump supremum suffices for
locally integrable variation on the usual adapted cadlag FV domain. The
original initial value need not be zero or integrable. -/
theorem hasLocallyIntegrableVariation_of_locally_integrable_runningJumpSupremum
    (hv : HasFiniteVariationPaths A P) (ha : Adapted F A) (hF : F.IsUsual P)
    (hc : HasCadlagPaths A P)
    (hJ : Locally (fun Y : ℝ≥0 → Ω → ℝ ↦ ∀ t, Integrable (Y t) P) F
      (fun t ω ↦ (eRunningJumpSupremum A t ω).toReal) P) :
    HasLocallyIntegrableVariation A F P := by
  let J : ℝ≥0 → Ω → ℝ := fun t ω ↦ (eRunningJumpSupremum A t ω).toReal
  obtain ⟨τ, hτ, hiτ⟩ := hJ
  let κ (n : ℕ) (_ : Ω) : WithTop ℝ≥0 := (((n + 1 : ℕ) : ℝ≥0) : WithTop ℝ≥0)
  have hκ : IsLocalizingSequence F κ P := by
    refine ⟨⟨fun n ↦ isStoppingTime_const F ((n + 1 : ℕ) : ℝ≥0), ?_⟩, ?_⟩
    · exact Eventually.of_forall fun _ ↦ WithTop.tendsto_coe_atTop.comp
        ((tendsto_natCast_atTop_atTop (R := ℝ≥0)).comp (tendsto_add_atTop_nat 1))
    · exact Eventually.of_forall fun _ n m hnm ↦
        WithTop.coe_le_coe.mpr (Nat.cast_le.mpr (Nat.succ_le_succ hnm))
  let σ := min τ κ
  have hσ : IsLocalizingSequence F σ P := hτ.min hκ
  have hloc : Locally (fun Y ↦ HasLocallyIntegrableVariation Y F P) F A P := by
    refine ⟨σ, hσ, fun n ↦ ?_⟩
    let T : ℝ≥0 := ((n + 1 : ℕ) : ℝ≥0)
    let E := {ω | 0 < σ n ω}
    let Y := MeasureTheory.stoppedProcess (fun t ↦ E.indicator (A t)) (σ n)
    let H : Ω → ℝ := MeasureTheory.stoppedProcess
      (fun t ↦ {ω | 0 < τ n ω}.indicator (J t)) (τ n) T
    let G : Ω → ℝ := fun ω ↦ ‖H ω‖
    have hiG : Integrable G P := (hiτ n T).norm
    have hE : MeasurableSet[F 0] E := (hσ.isStoppingTime n).measurableSet_gt 0
    have hcMask := hc.indicator E
    have hcY : HasCadlagPaths Y P := hcMask.stoppedProcess (σ n)
    have haY : Adapted F Y :=
      ((ha.indicator_initial hE).stronglyAdapted.stoppedProcess_of_usual hF
        hcMask.hasRightContinuousPaths (hσ.isStoppingTime n)).adapted
    have hvMask : HasFiniteVariationPaths (fun t ↦ E.indicator (A t)) P := by
      filter_upwards [hv] with ω hω
      by_cases hωE : ω ∈ E
      · simpa only [indicator_of_mem hωE] using hω
      · simp only [indicator_of_notMem hωE]
        exact (monotone_const.monotoneOn univ).locallyBoundedVariationOn
    have hvY : HasFiniteVariationPaths Y P := hvMask.stoppedProcess (σ n)
    have hσcap (ω : Ω) : σ n ω ≤ (T : WithTop ℝ≥0) := min_le_right _ _
    have hpos (ω : Ω) : 0 < σ n ω ↔ 0 < τ n ω := by
      change 0 < min (τ n ω) (T : WithTop ℝ≥0) ↔ 0 < τ n ω
      rw [lt_min_iff, and_iff_left]
      exact WithTop.coe_lt_coe.mpr (show (0 : ℝ≥0) < T from by dsimp only [T]; positivity)
    have heH (ω : Ω) : MeasureTheory.stoppedProcess
        (fun t ↦ {v | 0 < σ n v}.indicator (J t)) (σ n) T ω = H ω := by
      have hmin : min (T : WithTop ℝ≥0) (σ n ω) = min (T : WithTop ℝ≥0) (τ n ω) := by
        change min (T : WithTop ℝ≥0) (min (τ n ω) T) = min (T : WithTop ℝ≥0) (τ n ω)
        rw [min_eq_right (min_le_right _ _)]
        exact min_comm _ _
      simp only [MeasureTheory.stoppedProcess, indicator_apply, mem_ofPred_eq, hpos ω, hmin, H]
    have hjY : ∀ᵐ ω ∂P, ∀ t : ℝ≥0, 0 < t → ‖jumpProcess Y t ω‖ ≤ G ω := by
      filter_upwards [hc, hcMask, hcY] with ω hcω hmω hyω t _ht
      have hsup : (eRunningJumpSupremum Y T ω).toReal = H ω :=
        (hcω.eRunningJumpSupremum_toReal_masked_stoppedProcess (σ n) T).trans (heH ω)
      by_cases ht : t ≤ T
      · have hle : ENNReal.ofReal ‖jumpProcess Y t ω‖ ≤ eRunningJumpSupremum Y T ω :=
          le_iSup_of_le t (le_iSup_of_le ht le_rfl)
        have hb : ‖jumpProcess Y t ω‖ ≤ H ω := by
          have hr := ENNReal.toReal_mono (hyω.eRunningJumpSupremum_ne_top T) hle
          simpa only [ENNReal.toReal_ofReal (norm_nonneg _), hsup] using hr
        exact hb.trans (le_abs_self _)
      · have hnot : ¬ (t : WithTop ℝ≥0) ≤ σ n ω := fun h ↦
          ht (WithTop.coe_le_coe.mp (h.trans (hσcap ω)))
        have hjump := hmω.jumpProcess_stoppedProcess (σ n) t
        change jumpProcess Y t ω = _ at hjump
        rw [if_neg hnot] at hjump
        rw [hjump, norm_zero]
        exact norm_nonneg _
    exact hvY.hasLocallyIntegrableVariation_of_integrable_jump_envelope haY hF hcY hiG hjY
  exact hasLocallyIntegrableVariation_of_locally hF ha hc hloc

end HasFiniteVariationPaths
end ProbabilityTheory
