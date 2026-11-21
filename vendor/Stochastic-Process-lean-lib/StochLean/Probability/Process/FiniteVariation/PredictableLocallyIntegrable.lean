/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.FiniteVariation.BoundedJumpLocalization
public import StochLean.Probability.Process.FiniteVariation.LocallyIntegrableLocalization
public import StochLean.Probability.Process.Stopping.PredictableLargeJump
public import StochLean.Probability.Process.Stopping.LargeJumpThresholdLocalization
public import StochLean.Probability.Process.Stopping.AnnouncingLocalization
public import StochLean.Probability.Process.Path.JumpSampling

/-! # Predictable FV processes have locally integrable variation

The actual first jumps above successive integer thresholds are predictable
and tend almost surely to infinity. Their announcing sequences produce actual
localizers strictly before each positive large-jump time. At every level, the
native positive-lifetime masked stopped process therefore has bounded positive
jumps, including its stopping endpoint, and hence locally integrable variation.

The existing stable-property localization theorem removes this extra level of
localization. No new local predicate or localizing selector is introduced, and
neither zero nor integrable initial values are assumed. The conclusion concerns
the original process, not only an everywhere-good replacement.
-/

@[expose] public section

open ProbabilityTheory MeasureTheory Filter Set
open scoped NNReal Topology

namespace MeasureTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {F : Filtration ℝ≥0 mΩ}
  {P : Measure Ω} [IsProbabilityMeasure P] {A : ℝ≥0 → Ω → ℝ}

/-- A predictable cadlag finite-variation process has locally integrable
variation without any initial-value moment assumption. Both path hypotheses
may hold only almost surely. -/
theorem IsStronglyPredictable.hasLocallyIntegrableVariation
    (hA : IsStronglyPredictable F A) (hF : F.IsUsual P)
    (hc : HasCadlagPaths A P) (hv : HasFiniteVariationPaths A P) :
    HasLocallyIntegrableVariation A F P := by
  classical
  have ha : Adapted F A := hA.stronglyAdapted.adapted
  let τ (n : ℕ) := nextLargeJump A (((n + 1 : ℕ) : ℝ)) (fun _ ↦ 0)
  have hpτ (n : ℕ) : IsPredictableStoppingTime F (τ n) P :=
    hA.isPredictableStoppingTime_nextLargeJump_zero hF hc hv (by positivity)
  have hτ : IsLocalizingSequence F τ P :=
    ha.isLocalizingSequence_nextLargeJump_nat_threshold hF hc
  obtain ⟨σ, hσ, _, hle, hstrict, _⟩ :=
    hτ.toIsPreLocalizingSequence.exists_localizingSequence_lt_of_predictable hpτ hF
  apply hasLocallyIntegrableVariation_of_locally hF ha hc
  refine ⟨σ, hσ, fun n ↦ ?_⟩
  let E : Set Ω := {ω | 0 < σ n ω}
  let Y : ℝ≥0 → Ω → ℝ := fun t ↦ E.indicator (A t)
  let B := MeasureTheory.stoppedProcess Y (σ n)
  change HasLocallyIntegrableVariation B F P
  have hE : MeasurableSet[F 0] E := (hσ.isStoppingTime n).measurableSet_gt 0
  have haY : Adapted F Y := ha.indicator_initial hE
  have hcY : HasCadlagPaths Y P := hc.indicator E
  have hvY : HasFiniteVariationPaths Y P := by
    filter_upwards [hv] with ω hω
    by_cases hωE : ω ∈ E
    · simpa only [Y, indicator_of_mem hωE] using hω
    · simp only [Y, indicator_of_notMem hωE]
      exact (monotone_const.monotoneOn univ).locallyBoundedVariationOn
  have haB : Adapted F B :=
    (haY.stronglyAdapted.stoppedProcess_of_usual hF hcY.hasRightContinuousPaths
      (hσ.isStoppingTime n)).adapted
  have hcB : HasCadlagPaths B P := hcY.stoppedProcess (σ n)
  have hvB : HasFiniteVariationPaths B P := hvY.stoppedProcess (σ n)
  apply hvB.hasLocallyIntegrableVariation_of_jump_bound haB hF hcB
    (C := ((n + 1 : ℕ) : ℝ)) (by positivity)
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

end MeasureTheory
