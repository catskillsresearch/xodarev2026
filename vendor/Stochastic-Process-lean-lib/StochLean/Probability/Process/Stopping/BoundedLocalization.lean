/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.Stopping.ContinuousHitting
public import StochLean.Probability.Process.Measurability.ContinuousVersion
public import StochLean.Probability.Process.Path.Stopping
public import Mathlib.Probability.Process.LocalProperty

/-! # Bounded stopping sequences for continuous adapted processes

This construction requires no martingale or integrability assumption. It is the shared
path/stopping ingredient for localization both at infinity and up to a random lifetime.
-/

@[expose] public section

open ProbabilityTheory MeasureTheory Filter Set
open scoped NNReal ENNReal Topology

namespace MeasureTheory

theorem Adapted.exists_bounded_stoppingSequence
    {Ω : Type*} {mΩ : MeasurableSpace Ω} {F : Filtration ℝ≥0 mΩ}
    {P : Measure Ω} {X : ℝ≥0 → Ω → ℝ}
    (hX : Adapted F X) (hF : F.IsUsual P) (hcont : HasContinuousPaths X P)
    (C : ℝ≥0) (hzero : ∀ᵐ ω ∂P, ‖X 0 ω‖ ≤ C) :
    ∃ τ : ℕ → Ω → WithTop ℝ≥0, IsPreLocalizingSequence F τ P ∧ Monotone τ ∧
      ∀ n, ∀ᵐ ω ∂P, ∀ t, ‖stoppedProcess X (τ n) t ω‖ ≤ (C : ℝ) + n := by
  obtain ⟨Y, heq, hprog, hc⟩ :=
    hX.stronglyAdapted.exists_continuous_indistinguishable_of_usual hF hcont
  let τ : ℕ → Ω → WithTop ℝ≥0 := fun n ↦ hittingAfter Y {x | (C : ℝ) + n ≤ |x|} 0
  have hτ : ∀ n, IsStoppingTime F (τ n) := fun n ↦
    hprog.stronglyAdapted.adapted.isStoppingTime_hittingAfter_abs hc _
  have hmono : Monotone τ := by
    intro n m hnm ω
    exact hittingAfter_abs_mono (hc ω) (add_le_add le_rfl (Nat.cast_le.mpr hnm))
  have htop : ∀ ω, Tendsto (τ · ω) atTop (𝓝 ⊤) := by
    intro ω
    apply tendsto_nhds_top_mono' (tendsto_hittingAfter_abs_nat (hc ω))
    intro n
    exact hittingAfter_abs_mono (hc ω) (le_add_of_nonneg_left C.coe_nonneg)
  refine ⟨τ, ⟨hτ, ae_of_all _ htop⟩, hmono, fun n ↦ ?_⟩
  filter_upwards [heq.stoppedProcess (τ n), heq, hzero] with ω hstop hω hz t
  rw [hstop t, Real.norm_eq_abs]
  apply abs_stoppedProcess_hittingAfter_le (hc ω)
  rw [← hω 0, ← Real.norm_eq_abs]
  exact hz.trans (le_add_of_nonneg_right (Nat.cast_nonneg n))

end MeasureTheory
