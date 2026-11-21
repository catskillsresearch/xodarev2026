/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.LocalMartingale.FundamentalDecomposition
public import StochLean.Probability.Process.FiniteVariation.StoppedJumpStep
public import StochLean.Probability.Process.FiniteVariation.LocallyIntegrableAlgebra

/-! # Local integrable variation of a local-martingale stopping jump

The fundamental local-martingale decomposition separates a bounded-jump part
from a locally integrable-variation part.  Their actual jumps at an arbitrary
positive stopping time give the corresponding decomposition of the single
stopped-jump step.  Thus the step has locally integrable variation without any
global moment or finite-variation assumption on the original martingale.
-/

@[expose] public section

open MeasureTheory Filter Set
open scoped NNReal

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
  [IsProbabilityMeasure P] {F : Filtration ℝ≥0 mΩ}
  {M : ℝ≥0 → Ω → ℝ}

/-- The actual stopped-jump step of every local martingale has locally
integrable variation at a pointwise positive stopping time. -/
theorem IsLocalMartingale.stoppedJumpStep_hasLocallyIntegrableVariation
    (hM : IsLocalMartingale M F P) (hF : F.IsUsual P)
    {τ : Ω → WithTop ℝ≥0} (hτ : IsStoppingTime F τ)
    (hpos : ∀ ω, 0 < τ ω) :
    HasLocallyIntegrableVariation (stoppedJumpStep M τ) F P := by
  obtain ⟨N, D, hN, hD, _, _, hvD, hsplit, hjN, _⟩ :=
    hM.exists_fundamental_decomposition_of_pos hF (β := 1) zero_lt_one
  let JN := stoppedValueWithTerminal (jumpProcess N) (fun _ ↦ (0 : ℝ)) τ
  have hmJN : StronglyMeasurable JN :=
    (hN.1.stronglyMeasurable_stopped_jump_of_usual hF hN.2.1 hτ).mono
      hτ.measurableSpace_le
  have hbJN : ∀ᵐ ω ∂P, ‖JN ω‖ ≤ (2 : ℝ) := by
    filter_upwards [hN.2.1, hjN] with ω hcω hjω
    cases ht : τ ω with
    | top =>
        simp only [JN, stoppedValueWithTerminal_jump_eq_zero_of_top ht, norm_zero]
        norm_num
    | coe t =>
        change ‖stoppedValueWithTerminal (jumpProcess N) (fun _ ↦ (0 : ℝ)) τ ω‖ ≤ 2
        rw [stoppedValueWithTerminal_jump_eq_of_eq_coe ht]
        have htpos : 0 < t := WithTop.coe_lt_coe.mp (ht ▸ hpos ω)
        simpa only [mul_one] using hjω t htpos
  have hiJN : Integrable JN P :=
    (integrable_const (2 : ℝ)).mono' hmJN.aestronglyMeasurable hbJN
  have hvUNglobal : HasIntegrableVariation (stoppedJumpStep N τ) P := by
    exact hasIntegrableVariation_indicator_lifetime_le hτ.measurable' hiJN
  have hvUN : HasLocallyIntegrableVariation (stoppedJumpStep N τ) F P :=
    hvUNglobal.hasLocallyIntegrableVariation
  have hvUD : HasLocallyIntegrableVariation (stoppedJumpStep D τ) F P :=
    hvD.stoppedJumpStep_hasLocallyIntegrableVariation hD.1 hF hD.2.1 hτ hpos
  have haUN : Adapted F (stoppedJumpStep N τ) :=
    ProbabilityTheory.Adapted.adapted_stoppedJumpStep_of_usual hN.1 hF hN.2.1 hτ
  have haUD : Adapted F (stoppedJumpStep D τ) :=
    ProbabilityTheory.Adapted.adapted_stoppedJumpStep_of_usual hD.1 hF hD.2.1 hτ
  have hcUN : HasCadlagPaths (stoppedJumpStep N τ) P :=
    hasCadlagPaths_stoppedJumpStep N τ
  have hcUD : HasCadlagPaths (stoppedJumpStep D τ) P :=
    hasCadlagPaths_stoppedJumpStep D τ
  have hvSum := hvUN.add hvUD haUN haUD hF hcUN hcUD
  have he : Indistinguishable (stoppedJumpStep M τ)
      (stoppedJumpStep N τ + stoppedJumpStep D τ) P := by
    filter_upwards [hM.2.1, hN.2.1, hD.2.1] with ω hMc hNc hDc
    have hJ : stoppedValueWithTerminal (jumpProcess M) (fun _ ↦ (0 : ℝ)) τ ω =
        stoppedValueWithTerminal (jumpProcess N) (fun _ ↦ (0 : ℝ)) τ ω +
          stoppedValueWithTerminal (jumpProcess D) (fun _ ↦ (0 : ℝ)) τ ω := by
      cases ht : τ ω with
      | top =>
          simp only [stoppedValueWithTerminal_jump_eq_zero_of_top ht, add_zero]
      | coe t =>
          rw [stoppedValueWithTerminal_jump_eq_of_eq_coe ht,
            stoppedValueWithTerminal_jump_eq_of_eq_coe ht,
            stoppedValueWithTerminal_jump_eq_of_eq_coe ht]
          have hj := hNc.jumpProcess_add hDc t
          rw [← hsplit] at hj
          exact hj
    intro t
    by_cases ht : τ ω ≤ (t : WithTop ℝ≥0)
    · simp only [stoppedJumpStep, Pi.add_apply,
        indicator_of_mem (show ω ∈ {ω | τ ω ≤ (t : WithTop ℝ≥0)} from ht), hJ]
    · simp only [stoppedJumpStep, Pi.add_apply,
        indicator_of_notMem (show ω ∉ {ω | τ ω ≤ (t : WithTop ℝ≥0)} from ht),
        add_zero]
  exact hvSum.congr he.symm

end ProbabilityTheory
