/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.Semimartingale.Localization
public import StochLean.Probability.Process.Stopping.Before

/-! # Protter II.6 with the source `T-` stopping convention -/

@[expose] public section

open MeasureTheory Filter
open scoped NNReal Topology

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {F : Filtration ℝ≥0 mΩ}
  {P : Measure Ω} [IsFiniteMeasure P] {X : ℝ≥0 → Ω → ℝ}

/-- Equality after `T_n-` stopping gives source patching. Positivity and monotonicity of
the lifetimes from the printed statement are unnecessary: measurable AE divergence suffices. -/
theorem isSemimartingale_of_stoppedProcessBefore_eq (ha : Adapted F X)
    (hc : HasCadlagPaths X P) (Y : ℕ → ℝ≥0 → Ω → ℝ)
    (hY : ∀ n, IsSemimartingale (Y n) F P) (τ : ℕ → Ω → WithTop ℝ≥0)
    (hm : ∀ n, Measurable (τ n))
    (hlim : ∀ᵐ ω ∂P, Tendsto (fun n ↦ τ n ω) atTop (𝓝 ⊤))
    (heq : ∀ n, stoppedProcessBefore X (τ n) = stoppedProcessBefore (Y n) (τ n)) :
    IsSemimartingale X F P := by
  apply isSemimartingale_of_agree_before_lifetimes ha hc Y hY τ hm hlim
  intro n ω t ht
  have h := congrArg (fun Z : ℝ≥0 → Ω → ℝ ↦ Z t ω) (heq n)
  simpa only [stoppedProcessBefore_eq_of_lt _ ht] using h

/-- The common-event indistinguishability version of source `T-` patching. -/
theorem isSemimartingale_of_stoppedProcessBefore_indistinguishable (ha : Adapted F X)
    (hc : HasCadlagPaths X P) (Y : ℕ → ℝ≥0 → Ω → ℝ)
    (hY : ∀ n, IsSemimartingale (Y n) F P) (τ : ℕ → Ω → WithTop ℝ≥0)
    (hm : ∀ n, Measurable (τ n))
    (hlim : ∀ᵐ ω ∂P, Tendsto (fun n ↦ τ n ω) atTop (𝓝 ⊤))
    (heq : ∀ n, Indistinguishable
      (stoppedProcessBefore X (τ n)) (stoppedProcessBefore (Y n) (τ n)) P) :
    IsSemimartingale X F P := by
  apply isSemimartingale_of_ae_agree_before_lifetimes ha hc Y hY τ hm hlim
  intro n
  filter_upwards [heq n] with ω hω t ht
  simpa only [stoppedProcessBefore_eq_of_lt _ ht] using hω t

end ProbabilityTheory
