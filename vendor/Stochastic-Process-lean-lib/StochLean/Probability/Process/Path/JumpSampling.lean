/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.Path.JumpStopping
public import StochLean.Probability.Process.Stopping.JumpCoefficients

/-! # Actual jump samples of masked stopped paths

The stopping endpoint is included. A sample at infinity has explicit terminal
zero, even if the stopping lifetime is also infinite. The identity includes
time zero with the source convention `jumpProcess X 0 = X 0`.
Neither masks nor lifetimes need measurability for this pathwise statement.
-/

@[expose] public section

open MeasureTheory Set
open scoped NNReal

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
  {X : ℝ≥0 → Ω → ℝ} {ω : Ω}

theorem IsCadlagPath.stoppedValueWithTerminal_jump_masked_stoppedProcess
    (hX : IsCadlagPath (X · ω)) (E : Set Ω) (ρ σ : Ω → WithTop ℝ≥0) :
    stoppedValueWithTerminal
      (jumpProcess (MeasureTheory.stoppedProcess (fun t ↦ E.indicator (X t)) ρ))
      (fun _ ↦ (0 : ℝ)) σ ω =
        E.indicator ({ω | σ ω ≤ ρ ω}.indicator
          (stoppedValueWithTerminal (jumpProcess X) (fun _ ↦ (0 : ℝ)) σ)) ω := by
  classical
  cases hσ : σ ω with
  | top =>
    simp only [stoppedValueWithTerminal_jump_eq_zero_of_top hσ, indicator_apply]
    split_ifs <;> rfl
  | coe t =>
    have hm : IsCadlagPath (fun u ↦ E.indicator (X u) ω) := by
      by_cases hE : ω ∈ E
      · simpa only [indicator_of_mem hE] using hX
      · simp only [indicator_of_notMem hE]
        exact IsContinuousPath.isCadlagPath continuous_const
    have hj : jumpProcess (fun u ↦ E.indicator (X u)) t ω =
        E.indicator (jumpProcess X t) ω := by
      by_cases hE : ω ∈ E
      · simp [jumpProcess, leftLimitProcess, hE]
      · simp only [jumpProcess, Pi.sub_apply, leftLimitProcess, indicator_of_notMem hE]
        rw [(continuous_const : Continuous (fun _ : ℝ≥0 ↦ (0 : ℝ))).continuousWithinAt.leftLim_eq]
        split_ifs <;> simp only [sub_self]
    rw [stoppedValueWithTerminal_jump_eq_of_eq_coe hσ,
      hm.jumpProcess_stoppedProcess ρ t, hj]
    by_cases hE : ω ∈ E <;> by_cases hle : (t : WithTop ℝ≥0) ≤ ρ ω <;>
      simp only [indicator_apply, hE, hσ, hle, mem_ofPred_eq, if_true, if_false,
        stoppedValueWithTerminal_jump_eq_of_eq_coe hσ]

theorem HasCadlagPaths.ae_stoppedValueWithTerminal_jump_masked_stoppedProcess
    (hX : HasCadlagPaths X P) (E : Set Ω) (ρ σ : Ω → WithTop ℝ≥0) :
    stoppedValueWithTerminal
      (jumpProcess (MeasureTheory.stoppedProcess (fun t ↦ E.indicator (X t)) ρ))
      (fun _ ↦ (0 : ℝ)) σ =ᵐ[P]
        E.indicator ({ω | σ ω ≤ ρ ω}.indicator
          (stoppedValueWithTerminal (jumpProcess X) (fun _ ↦ (0 : ℝ)) σ)) :=
  hX.mono fun _ hω ↦ hω.stoppedValueWithTerminal_jump_masked_stoppedProcess E ρ σ

end ProbabilityTheory
