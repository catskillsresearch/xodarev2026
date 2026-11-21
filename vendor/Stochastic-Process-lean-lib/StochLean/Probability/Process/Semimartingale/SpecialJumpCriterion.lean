/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.Semimartingale.SpecialRunningSupremum
public import StochLean.Probability.Process.FiniteVariation.JumpEnvelopeLocalization
public import StochLean.Probability.Process.FiniteVariation.LocallyIntegrableLocalization
public import StochLean.Probability.Process.Path.JumpSampling
public import StochLean.Probability.Process.Path.LeftLimitAddition

/-! # The running-jump criterion for a classical semimartingale

The classical decomposition is used to construct the local integrability of
its actual FV part. Joint native localizers give the martingale part an
integrable whole-path envelope and the original jump supremum an integrable
value at an integer cap. Their sum bounds every positive jump of the native
masked stopped FV part, including the stopping endpoint. The existing jump
envelope and iterated-localization theorems then supply local integrable
variation, whose actual predictable compensation produces specialness.

The criterion uses the original all-times jump supremum with its initial
jump, not a dense jump grid. Initial constants disappear only in positive-time
jump identities. No initial moment, proposed compensator, or good-integrator
converse is assumed. Both directions stay within the classical source domain.
-/

@[expose] public section

open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology

namespace ProbabilityTheory

variable {Ω : Type*}

private theorem jump_masked_stopped_eq_of_le {Z : ℝ≥0 → Ω → ℝ} {ω : Ω}
    (hc : IsCadlagPath (Z · ω)) (τ : Ω → WithTop ℝ≥0) (t : ℝ≥0)
    (hp : 0 < τ ω) (ht : (t : WithTop ℝ≥0) ≤ τ ω) :
    jumpProcess (MeasureTheory.stoppedProcess
      (fun s ↦ {v | 0 < τ v}.indicator (Z s)) τ) t ω = jumpProcess Z t ω := by
  have h := hc.stoppedValueWithTerminal_jump_masked_stoppedProcess
    {v | 0 < τ v} τ (fun _ ↦ (t : WithTop ℝ≥0))
  simpa only [indicator_of_mem (show ω ∈ {v | 0 < τ v} from hp),
    indicator_of_mem (show ω ∈ {v | (t : WithTop ℝ≥0) ≤ τ v} from ht),
    stoppedValueWithTerminal_jump_eq_of_eq_coe
      (τ := fun _ : Ω ↦ (t : WithTop ℝ≥0)) (ω := ω) rfl] using h

variable {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
  {F : Filtration ℝ≥0 mΩ} {X : ℝ≥0 → Ω → ℝ}

/-- Protter III.36, converse on the classical source domain. Actual local
integrability of the running jump supremum constructs a special decomposition;
no local-integrability property of a proposed FV part is supplied as an input. -/
theorem IsClassicalSemimartingale.isSpecialSemimartingale_of_locally_integrable_runningJumpSupremum
    (hX : IsClassicalSemimartingale X F P) (hF : F.IsUsual P)
    (hJ : Locally (fun Y : ℝ≥0 → Ω → ℝ ↦ ∀ t, Integrable (Y t) P) F
      (fun t ω ↦ (eRunningJumpSupremum X t ω).toReal) P) :
    IsSpecialSemimartingale X F P := by
  classical
  obtain ⟨haX, hcX, M, A, hM, haA, hcA, hvA, hM0, hA0, he⟩ := hX
  have hjA : ∀ᵐ ω ∂P, ∀ t : ℝ≥0, 0 < t →
      jumpProcess A t ω = jumpProcess X t ω - jumpProcess M t ω := by
    filter_upwards [he.jumpProcess, hM.2.1, hcA] with ω heω hmω haω t ht
    let I : ℝ≥0 → Ω → ℝ := fun _ ↦ X 0
    have hcI : IsContinuousPath (I · ω) := continuous_const
    have hsum : IsCadlagPath ((I + M) · ω) := hcI.isCadlagPath.add hmω
    have hj := heω t
    change jumpProcess X t ω = jumpProcess ((I + M) + A) t ω at hj
    rw [hsum.jumpProcess_add haω t, hcI.isCadlagPath.jumpProcess_add hmω t,
      hcI.jumpProcess_eq_zero (ne_of_gt ht), zero_add] at hj
    linarith only [hj]
  obtain ⟨τ, hτ, hG⟩ := hM.locally_integrable_envelope hF
  obtain ⟨σ, hσ, hiσ⟩ := hJ
  let κ (n : ℕ) (_ : Ω) : WithTop ℝ≥0 := (((n + 1 : ℕ) : ℝ≥0) : WithTop ℝ≥0)
  have hκ : IsLocalizingSequence F κ P := by
    refine ⟨⟨fun n ↦ isStoppingTime_const F ((n + 1 : ℕ) : ℝ≥0), ?_⟩, ?_⟩
    · exact Eventually.of_forall fun _ ↦ WithTop.tendsto_coe_atTop.comp
        ((tendsto_natCast_atTop_atTop (R := ℝ≥0)).comp (tendsto_add_atTop_nat 1))
    · exact Eventually.of_forall fun _ n m hnm ↦
        WithTop.coe_le_coe.mpr (Nat.cast_le.mpr (Nat.succ_le_succ hnm))
  let ρ := min (min τ σ) κ
  have hρ : IsLocalizingSequence F ρ P := (hτ.min hσ).min hκ
  have hloc : Locally (fun Y ↦ HasLocallyIntegrableVariation Y F P) F A P := by
    refine ⟨ρ, hρ, fun n ↦ ?_⟩
    obtain ⟨G, hiG, hbG⟩ := hG n
    let T : ℝ≥0 := ((n + 1 : ℕ) : ℝ≥0)
    let E : Set Ω := {ω | 0 < ρ n ω}
    let Y := MeasureTheory.stoppedProcess (fun t ↦ E.indicator (A t)) (ρ n)
    let U := MeasureTheory.stoppedProcess
      (fun t ↦ {ω | 0 < τ n ω}.indicator (M t)) (τ n)
    let V := MeasureTheory.stoppedProcess
      (fun t ↦ {ω | 0 < σ n ω}.indicator (X t)) (σ n)
    let H : Ω → ℝ := MeasureTheory.stoppedProcess
      (fun t ↦ {ω | 0 < σ n ω}.indicator
        (fun ω ↦ (eRunningJumpSupremum X t ω).toReal)) (σ n) T
    let K : Ω → ℝ := fun ω ↦ 2 * G ω + ‖H ω‖
    have hiK : Integrable K P := (hiG.const_mul 2).add (hiσ n T).norm
    change ∀ᵐ ω ∂P, ∀ t, ‖U t ω‖ ≤ G ω at hbG
    have hE : MeasurableSet[F 0] E := (hρ.isStoppingTime n).measurableSet_gt 0
    have hcMask := hcA.indicator E
    have hcY : HasCadlagPaths Y P := hcMask.stoppedProcess (ρ n)
    have haY : Adapted F Y :=
      ((haA.indicator_initial hE).stronglyAdapted.stoppedProcess_of_usual hF
        hcMask.hasRightContinuousPaths (hρ.isStoppingTime n)).adapted
    have hvMask : HasFiniteVariationPaths (fun t ↦ E.indicator (A t)) P := by
      filter_upwards [hvA] with ω hω
      by_cases hωE : ω ∈ E
      · simpa only [indicator_of_mem hωE] using hω
      · simp only [indicator_of_notMem hωE]
        exact (monotone_const.monotoneOn univ).locallyBoundedVariationOn
    have hvY : HasFiniteVariationPaths Y P := hvMask.stoppedProcess (ρ n)
    have hcU : HasCadlagPaths U P :=
      (hM.2.1.indicator {ω | 0 < τ n ω}).stoppedProcess (τ n)
    have hcV : HasCadlagPaths V P :=
      (hcX.indicator {ω | 0 < σ n ω}).stoppedProcess (σ n)
    have hρτ (ω : Ω) : ρ n ω ≤ τ n ω :=
      (min_le_left _ _).trans (min_le_left _ _)
    have hρσ (ω : Ω) : ρ n ω ≤ σ n ω :=
      (min_le_left _ _).trans (min_le_right _ _)
    have hρcap (ω : Ω) : ρ n ω ≤ (T : WithTop ℝ≥0) := min_le_right _ _
    have hjY : ∀ᵐ ω ∂P, ∀ t : ℝ≥0, 0 < t → ‖jumpProcess Y t ω‖ ≤ K ω := by
      filter_upwards [hcX, hcA, hM.2.1, hcU, hcV, hbG, hjA]
        with ω hxω haω hmω huω hvω hbω hjω t ht
      have hG0 : 0 ≤ G ω := (norm_nonneg (U 0 ω)).trans (hbω 0)
      have hK0 : 0 ≤ K ω := add_nonneg (mul_nonneg (by norm_num) hG0) (norm_nonneg _)
      have hsamp := haω.stoppedValueWithTerminal_jump_masked_stoppedProcess E (ρ n)
        (fun _ ↦ (t : WithTop ℝ≥0))
      rw [stoppedValueWithTerminal_jump_eq_of_eq_coe
        (τ := fun _ : Ω ↦ (t : WithTop ℝ≥0)) (ω := ω) rfl] at hsamp
      change jumpProcess Y t ω = _ at hsamp
      by_cases hp : ω ∈ E
      · rw [indicator_of_mem hp] at hsamp
        by_cases htr : (t : WithTop ℝ≥0) ≤ ρ n ω
        · rw [indicator_of_mem
            (show ω ∈ {v | (t : WithTop ℝ≥0) ≤ ρ n v} from htr),
            stoppedValueWithTerminal_jump_eq_of_eq_coe
              (τ := fun _ : Ω ↦ (t : WithTop ℝ≥0)) (ω := ω) rfl] at hsamp
          have hpρ : 0 < ρ n ω := hp
          have htτ := htr.trans (hρτ ω)
          have htσ := htr.trans (hρσ ω)
          have htT : t ≤ T := WithTop.coe_le_coe.mp (htr.trans (hρcap ω))
          have heU : jumpProcess U t ω = jumpProcess M t ω :=
            jump_masked_stopped_eq_of_le hmω (τ n) t (hpρ.trans_le (hρτ ω)) htτ
          have heV : jumpProcess V t ω = jumpProcess X t ω :=
            jump_masked_stopped_eq_of_le hxω (σ n) t (hpρ.trans_le (hρσ ω)) htσ
          have hJM : ‖jumpProcess M t ω‖ ≤ 2 * G ω := by
            simpa only [heU] using huω.norm_jumpProcess_le_of_bound hbω t
          have hsup : (eRunningJumpSupremum V T ω).toReal = H ω :=
            hxω.eRunningJumpSupremum_toReal_masked_stoppedProcess (σ n) T
          have hJX : ‖jumpProcess X t ω‖ ≤ ‖H ω‖ := by
            have hle : ENNReal.ofReal ‖jumpProcess V t ω‖ ≤
                eRunningJumpSupremum V T ω := le_iSup_of_le t (le_iSup_of_le htT le_rfl)
            have hr := ENNReal.toReal_mono (hvω.eRunningJumpSupremum_ne_top T) hle
            have hxH : ‖jumpProcess X t ω‖ ≤ H ω := by
              simpa only [ENNReal.toReal_ofReal (norm_nonneg _), heV, hsup] using hr
            exact hxH.trans (le_abs_self _)
          rw [hsamp, hjω t ht]
          have hb := (norm_sub_le _ _).trans (add_le_add hJX hJM)
          simpa only [K, add_comm] using hb
        · rw [indicator_of_notMem
            (show ω ∉ {v | (t : WithTop ℝ≥0) ≤ ρ n v} from htr)] at hsamp
          rw [hsamp, norm_zero]
          exact hK0
      · rw [indicator_of_notMem hp] at hsamp
        rw [hsamp, norm_zero]
        exact hK0
    exact hvY.hasLocallyIntegrableVariation_of_integrable_jump_envelope haY hF hcY hiK hjY
  have hlocalA : HasLocallyIntegrableVariation A F P :=
    hasLocallyIntegrableVariation_of_locally hF haA hcA hloc
  exact (isSpecialSemimartingale_iff_exists_locallyIntegrableVariation_decomposition hF).mpr
    ⟨haX, hcX, M, A, hM, haA, hcA, hlocalA, hM0, hA0, he⟩

/-- Protter III.36 on the classical source domain, using the original actual
running jump supremum and Mathlib's native masked local-integrability property. -/
theorem IsClassicalSemimartingale.isSpecialSemimartingale_iff_locally_integrable_runningJumpSupremum
    (hX : IsClassicalSemimartingale X F P) (hF : F.IsUsual P) :
    IsSpecialSemimartingale X F P ↔
      Locally (fun Y : ℝ≥0 → Ω → ℝ ↦ ∀ t, Integrable (Y t) P) F
        (fun t ω ↦ (eRunningJumpSupremum X t ω).toReal) P :=
  ⟨fun h ↦ h.locally_integrable_runningJumpSupremum hF,
    hX.isSpecialSemimartingale_of_locally_integrable_runningJumpSupremum hF⟩

end ProbabilityTheory
