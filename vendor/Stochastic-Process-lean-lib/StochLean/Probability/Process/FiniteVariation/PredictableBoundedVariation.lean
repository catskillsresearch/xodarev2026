/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.FiniteVariation.BoundedJumpLocalization
public import StochLean.Probability.Process.Stopping.PredictableLargeJump
public import StochLean.Probability.Process.Stopping.LargeJumpThresholdLocalization
public import StochLean.Probability.Process.Stopping.AnnouncingLocalization
public import StochLean.Probability.Process.Stopping.PredictableProcess
public import StochLean.Probability.Process.Path.JumpSampling

/-! # Deterministic total-variation budgets for predictable FV localizations

The actual predictable large-jump times admit localizers strictly before them.
The first localization therefore bounds every positive jump, including its
stopping endpoint. The existing capped exits of the total-variation process
then bound the actual whole-half-line variation by a deterministic constant.
Native stable-property idempotence combines these two localizations.

The predictable and cadlag properties concern the actual masked stopped
processes. No new variation, local predicate, or localizer selector is defined.
The variation budget excludes any initial atom, so the original initial value
need not vanish or have any moment. In particular, this deterministic budget
is stronger than merely having an integrable random variation envelope.
-/

@[expose] public section

open ProbabilityTheory MeasureTheory Filter Set
open scoped NNReal ENNReal Topology

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {F : Filtration ℝ≥0 mΩ}
  {P : Measure Ω} {A : ℝ≥0 → Ω → ℝ}

private theorem predictable_cadlag_masked_stoppedProcess
    (hp : IsStronglyPredictable F A) (hc : HasCadlagPaths A P)
    {τ : Ω → WithTop ℝ≥0} (hτ : IsStoppingTime F τ) :
    IsStronglyPredictable F
      (stoppedProcess (fun t ↦ {ω | 0 < τ ω}.indicator (A t)) τ) ∧
      HasCadlagPaths
        (stoppedProcess (fun t ↦ {ω | 0 < τ ω}.indicator (A t)) τ) P := by
  classical
  let E : Set Ω := {ω | 0 < τ ω}
  have hE : MeasurableSet[F 0] E := hτ.measurableSet_gt 0
  let K : ℝ≥0 → Ω → ℝ := fun _ ω ↦ if ω ∈ E then 1 else 0
  have haK : Adapted F K := fun t ↦
    Measurable.ite (F.mono bot_le _ hE) measurable_const measurable_const
  have hpK : IsStronglyPredictable F K :=
    haK.isStronglyPredictable_of_leftContinuous (fun _ _ ↦ continuousWithinAt_const)
  have he : (fun t ↦ E.indicator (A t)) = A * K := by
    ext t ω
    by_cases hω : ω ∈ E <;> simp [K, hω]
  have hpMask : IsStronglyPredictable F (fun t ↦ E.indicator (A t)) := by
    rw [he]
    exact hp.mul hpK
  exact ⟨hpMask.stoppedProcess hτ, (hc.indicator E).stoppedProcess τ⟩

/-- Actual predictability, cadlag paths, and a deterministic bound on the
whole variation are stable under the native positive-lifetime masked stop.
No moment assumption, usual condition, or finiteness of the measure is needed. -/
theorem isStable_predictable_cadlag_boundedTotalVariation :
    IsStable F (fun Y : ℝ≥0 → Ω → ℝ ↦ IsStronglyPredictable F Y ∧
      HasCadlagPaths Y P ∧ ∃ C : ℝ, 0 ≤ C ∧
        ∀ᵐ ω ∂P, eVariationOn (Y · ω) univ ≤ ENNReal.ofReal C) := by
  rintro Y ⟨hp, hc, C, hC, hb⟩ τ hτ
  have hs := predictable_cadlag_masked_stoppedProcess hp hc hτ
  refine ⟨hs.1, hs.2, C, hC, ?_⟩
  filter_upwards [hb] with ω hω
  change eVariationOn (fun t ↦ stoppedProcess
    (fun s ↦ {ω | 0 < τ ω}.indicator (Y s)) τ t ω) univ ≤ ENNReal.ofReal C
  rw [eVariationOn_univ_stoppedProcess_indicator_pos]
  exact (eVariationOn_univ_stoppedProcess_le Y τ ω).trans hω

end ProbabilityTheory

namespace MeasureTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {F : Filtration ℝ≥0 mΩ}
  {P : Measure Ω} [IsProbabilityMeasure P] {A : ℝ≥0 → Ω → ℝ}

/-- A predictable cadlag FV process has actual native localizations with
deterministically bounded whole-half-line variation. The original initial
value is unrestricted, and both source path hypotheses may hold only AE. -/
theorem IsStronglyPredictable.locally_boundedTotalVariation
    (hA : IsStronglyPredictable F A) (hF : F.IsUsual P)
    (hc : HasCadlagPaths A P) (hv : HasFiniteVariationPaths A P) :
    Locally (fun Y ↦ IsStronglyPredictable F Y ∧ HasCadlagPaths Y P ∧
      ∃ C : ℝ, 0 ≤ C ∧ ∀ᵐ ω ∂P,
        eVariationOn (Y · ω) univ ≤ ENNReal.ofReal C) F A P := by
  classical
  let : F.IsRightContinuous := hF.rightContinuous
  have ha : Adapted F A := hA.stronglyAdapted.adapted
  let τ (n : ℕ) := nextLargeJump A (((n + 1 : ℕ) : ℝ)) (fun _ ↦ 0)
  have hpτ (n : ℕ) : IsPredictableStoppingTime F (τ n) P :=
    hA.isPredictableStoppingTime_nextLargeJump_zero hF hc hv (by positivity)
  have hτ : IsLocalizingSequence F τ P :=
    ha.isLocalizingSequence_nextLargeJump_nat_threshold hF hc
  obtain ⟨σ, hσ, _, hle, hstrict, _⟩ :=
    hτ.toIsPreLocalizingSequence.exists_localizingSequence_lt_of_predictable hpτ hF
  apply (isStable_predictable_cadlag_boundedTotalVariation (F := F) (P := P)).locally_locally_iff.mp
  refine ⟨σ, hσ, fun n ↦ ?_⟩
  let E : Set Ω := {ω | 0 < σ n ω}
  let Y : ℝ≥0 → Ω → ℝ := fun t ↦ E.indicator (A t)
  let B := MeasureTheory.stoppedProcess Y (σ n)
  change Locally (fun Z ↦ IsStronglyPredictable F Z ∧ HasCadlagPaths Z P ∧
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᵐ ω ∂P,
      eVariationOn (Z · ω) univ ≤ ENNReal.ofReal C) F B P
  have hs := predictable_cadlag_masked_stoppedProcess hA hc (hσ.isStoppingTime n)
  have hpB : IsStronglyPredictable F B := hs.1
  have hcB : HasCadlagPaths B P := hs.2
  have haB : Adapted F B := hpB.stronglyAdapted.adapted
  have hvY : HasFiniteVariationPaths Y P := by
    filter_upwards [hv] with ω hω
    by_cases hωE : ω ∈ E
    · simpa only [Y, indicator_of_mem hωE] using hω
    · simp only [Y, indicator_of_notMem hωE]
      exact (monotone_const.monotoneOn univ).locallyBoundedVariationOn
  have hvB : HasFiniteVariationPaths B P := hvY.stoppedProcess (σ n)
  have hjB : ∀ᵐ ω ∂P, ∀ t : ℝ≥0, 0 < t →
      ‖jumpProcess B t ω‖ ≤ ((n + 1 : ℕ) : ℝ) := by
    filter_upwards [hc] with ω hcω t ht
    have hj := hcω.stoppedValueWithTerminal_jump_masked_stoppedProcess E (σ n)
      (fun _ ↦ (t : WithTop ℝ≥0))
    rw [stoppedValueWithTerminal_jump_eq_of_eq_coe
      (τ := fun _ : Ω ↦ (t : WithTop ℝ≥0)) (ω := ω) rfl] at hj
    change jumpProcess B t ω = _ at hj
    by_cases hωE : ω ∈ E
    · rw [indicator_of_mem hωE] at hj
      by_cases hts : (t : WithTop ℝ≥0) ≤ σ n ω
      · rw [indicator_of_mem (show ω ∈ {ω | (t : WithTop ℝ≥0) ≤ σ n ω} from hts),
          stoppedValueWithTerminal_jump_eq_of_eq_coe
            (τ := fun _ : Ω ↦ (t : WithTop ℝ≥0)) (ω := ω) rfl] at hj
        rw [hj]
        apply le_of_not_gt
        intro hlarge
        have htτ : (0 : WithTop ℝ≥0) < τ n ω :=
          (WithTop.coe_lt_coe.mpr ht).trans_le (hts.trans (hle n ω))
        have hτt : τ n ω ≤ (t : WithTop ℝ≥0) :=
          nextLargeJump_le_of_jump (WithTop.coe_lt_coe.mpr ht) hlarge
        exact (not_lt_of_ge (hτt.trans hts)) (hstrict n ω htτ)
      · rw [indicator_of_notMem
          (show ω ∉ {ω | (t : WithTop ℝ≥0) ≤ σ n ω} from hts)] at hj
        rw [hj, norm_zero]
        positivity
    · rw [indicator_of_notMem hωE] at hj
      rw [hj, norm_zero]
      positivity
  have haV := haB.totalVariationProcess_of_usual hF hcB
  have hcV := hvB.hasCadlagPaths_totalVariationProcess hcB.hasRightContinuousPaths
  have hρ := haV.isLocalizingSequence_cappedNormExitSequence hF hcV
  refine ⟨cappedNormExitSequence (totalVariationProcess B), hρ, fun m ↦ ?_⟩
  have hsm := predictable_cadlag_masked_stoppedProcess hpB hcB (hρ.isStoppingTime m)
  refine ⟨hsm.1, hsm.2, ((m + 1 : ℕ) : ℝ) + ((n + 1 : ℕ) : ℝ), by positivity, ?_⟩
  have hvar := (hvB.hasIntegrableVariation_stopped_totalVariation_exit_of_jump_bound
    haB hF hcB (by positivity) hjB m).2
  filter_upwards [hvar] with ω hω
  change eVariationOn (fun t ↦ MeasureTheory.stoppedProcess
    (fun s ↦ {ω | 0 < cappedNormExitSequence (totalVariationProcess B) m ω}.indicator (B s))
    (cappedNormExitSequence (totalVariationProcess B) m) t ω) univ ≤ _
  rw [eVariationOn_univ_stoppedProcess_indicator_pos]
  exact hω

end MeasureTheory
