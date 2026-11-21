/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.Stopping.JumpExitIntegrability

/-! # Removing the complete actual jump at a capped norm exit

The stopped path minus the closed step carrying its complete exit jump stays
within the deterministic exit level. No jump-amplitude selection, inaccessible
jump assumption, or initial normalization is involved. At a zero exit the
source jump equals the original initial value, so the residual is zero.

The capped exit is proved finite before any finite-time evaluation. The
almost-sure result uses one common cadlag event for every exit and every time.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal

namespace ProbabilityTheory

variable {Ω : Type*} {X : ℝ≥0 → Ω → ℝ} {ω : Ω}

/-- Subtracting the entire exit jump, including the source initial jump when
the exit is zero, leaves the actual stopped path uniformly bounded. -/
theorem IsCadlagPath.norm_stoppedProcess_sub_exit_jump_le
    (hc : IsCadlagPath (X · ω)) (n : ℕ) (t : ℝ≥0) :
    ‖stoppedProcess X (cappedNormExitSequence X n) t ω -
      {v | cappedNormExitSequence X n v ≤ (t : WithTop ℝ≥0)}.indicator
        (stoppedValueWithTerminal (jumpProcess X) (fun _ ↦ (0 : ℝ))
          (cappedNormExitSequence X n)) ω‖ ≤ ((n + 1 : ℕ) : ℝ) := by
  by_cases ht : cappedNormExitSequence X n ω ≤ (t : WithTop ℝ≥0)
  · have hmem : ω ∈ {v | cappedNormExitSequence X n v ≤ (t : WithTop ℝ≥0)} := ht
    rw [stoppedProcess_eq_of_ge ht, indicator_of_mem hmem,
      stoppedValueWithTerminal_of_ne_top (cappedNormExitSequence_ne_top X n ω)]
    change ‖X (cappedNormExitSequence X n ω).untopA ω -
      jumpProcess X (cappedNormExitSequence X n ω).untopA ω‖ ≤ _
    have he : ((cappedNormExitSequence X n ω).untopA : WithTop ℝ≥0) =
        cappedNormExitSequence X n ω := by
      rw [WithTop.untopA_eq_untop (cappedNormExitSequence_ne_top X n ω),
        WithTop.coe_untop]
    simpa only [jumpProcess, Pi.sub_apply, sub_sub_cancel] using
      hc.norm_leftLimitProcess_le_of_le_cappedNormExitSequence he.le
  · have hnot : ω ∉ {v | cappedNormExitSequence X n v ≤ (t : WithTop ℝ≥0)} := ht
    have hlt : (t : WithTop ℝ≥0) < cappedNormExitSequence X n ω := lt_of_not_ge ht
    rw [stoppedProcess_eq_of_le hlt.le, indicator_of_notMem hnot, sub_zero]
    exact norm_le_of_lt_cappedNormExitSequence hlt

variable {mΩ : MeasurableSpace Ω} {P : Measure Ω}

/-- One cadlag event gives the complete exit-jump residual bound simultaneously
at all levels and all times. There is no coordinatewise AE-to-path upgrade. -/
theorem HasCadlagPaths.ae_forall_norm_stoppedProcess_sub_exit_jump_le
    (hc : HasCadlagPaths X P) :
    ∀ᵐ ω ∂P, ∀ (n : ℕ) (t : ℝ≥0),
      ‖MeasureTheory.stoppedProcess X (cappedNormExitSequence X n) t ω -
        {v | cappedNormExitSequence X n v ≤ (t : WithTop ℝ≥0)}.indicator
          (stoppedValueWithTerminal (jumpProcess X) (fun _ ↦ (0 : ℝ))
            (cappedNormExitSequence X n)) ω‖ ≤ ((n + 1 : ℕ) : ℝ) := by
  exact hc.mono fun _ hω n t ↦ hω.norm_stoppedProcess_sub_exit_jump_le n t

end ProbabilityTheory
