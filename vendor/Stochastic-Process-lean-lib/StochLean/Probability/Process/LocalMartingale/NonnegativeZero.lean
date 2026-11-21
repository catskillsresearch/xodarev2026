/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.LocalMartingale.Bounded

/-! # A nonnegative local martingale starting at zero vanishes

The proof uses the actual masked UI fundamental sequence. Each localization
has zero expectation and is nonnegative, hence vanishes. Eventual localization
agreement and right continuity give one common event for all finite times.
-/

@[expose] public section

open MeasureTheory Filter Set
open scoped NNReal Topology

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
  {F : Filtration ℝ≥0 mΩ} [SigmaFiniteFiltration P F] {X : ℝ≥0 → Ω → ℝ}

theorem IsLocalMartingale.indistinguishable_zero_of_nonneg
    (hX : IsLocalMartingale X F P) (hn : ∀ᵐ ω ∂P, ∀ t : ℝ≥0, 0 ≤ X t ω)
    (h0 : X 0 =ᵐ[P] 0) : Indistinguishable X 0 P := by
  obtain ⟨τ, hτ⟩ := hX.2.2
  let Y := fun n ↦ stoppedProcess (fun t ↦ {ω | 0 < τ n ω}.indicator (X t)) (τ n)
  have hm (n : ℕ) : Martingale (Y n) F P := (hτ.2.2 n).1
  have hy0 (n : ℕ) : Y n 0 =ᵐ[P] 0 := by
    filter_upwards [h0] with ω hω
    change stoppedProcess (fun t ↦ {ω | 0 < τ n ω}.indicator (X t)) (τ n) 0 ω = 0
    rw [stoppedProcess_eq_of_le (show ((0 : ℝ≥0) : WithTop ℝ≥0) ≤ τ n ω from bot_le)]
    by_cases hp : 0 < τ n ω <;> simp [hp, hω]
  have hyp (n : ℕ) (t : ℝ≥0) : 0 ≤ᵐ[P] Y n t := by
    filter_upwards [hn] with ω hω
    change 0 ≤ stoppedProcess (fun t ↦ {ω | 0 < τ n ω}.indicator (X t)) (τ n) t ω
    rw [stoppedProcess_indicator_comm]
    by_cases hp : 0 < τ n ω
    · rw [indicator_of_mem (show ω ∈ {ω | 0 < τ n ω} from hp)]
      exact hω _
    · rw [indicator_of_notMem (show ω ∉ {ω | 0 < τ n ω} from hp)]
  have hy (n : ℕ) (t : ℝ≥0) : Y n t =ᵐ[P] 0 := by
    apply (integral_eq_zero_iff_of_nonneg_ae (hyp n t) ((hm n).integrable t)).mp
    have he := (hm n).setIntegral_eq (show (0 : ℝ≥0) ≤ t from bot_le) MeasurableSet.univ
    simp only [setIntegral_univ, integral_congr_ae (hy0 n), Pi.zero_apply, integral_zero] at he
    exact he.symm
  have hmod : IsModification X 0 P := by
    intro t
    have hall : ∀ᵐ ω ∂P, ∀ n, Y n t ω = 0 := by
      rw [ae_all_iff]
      exact fun n ↦ hy n t
    filter_upwards [hall, hτ.1.ae_eventually_masked_stoppedProcess_eq (X := X) t]
      with ω hyω he
    obtain ⟨n, hn⟩ := he.exists
    exact hn.symm.trans (hyω n)
  exact hmod.indistinguishable_of_rightContinuous hX.2.1.hasRightContinuousPaths
    (ae_of_all _ fun _ _ ↦ continuousWithinAt_const)

end ProbabilityTheory
