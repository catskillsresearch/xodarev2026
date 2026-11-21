/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.FiniteVariation.Natural
public import StochLean.Probability.Process.LocalMartingale.DeterministicStopping
public import StochLean.Probability.Process.Semimartingale.QuadraticCovariation.OneSidedStopping

/-! # Finite-time bracket means from naturality

Testing naturality with a bounded martingale stopped at a deterministic time
gives integrability and zero expectation of the original raw bracket at that
time. The one-sided stopping identity makes the tested bracket eventually
constant, so its actual terminal is constructed rather than supplied.

No martingale property of the bracket, predictable-jump theorem, or L2 bound
on the integrable-variation process is assumed. The same raw bracket is used
throughout; its initial product is never subtracted or discarded. All times
in the stopping identity lie on one common full-measure path event.
-/

@[expose] public section

open MeasureTheory Filter
open scoped NNReal ENNReal Topology

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsFiniteMeasure P]
  {F : Filtration ℝ≥0 mΩ} {A M : ℝ≥0 → Ω → ℝ}

/-- Naturality determines the integrability and mean of every deterministic
finite-time value of the actual mixed bracket. -/
theorem IsNatural.integrable_quadraticCovariation_and_integral_eq_zero
    {hF : F.IsUsual P} (hA : IsNatural A F P hF)
    (hM : Martingale M F P) (hcM : HasCadlagPaths M P) (C : ℝ) (hC : 0 ≤ C)
    (hb : ∀ᵐ ω ∂P, ∀ t, ‖M t ω‖ ≤ C) (T : ℝ≥0) :
    Integrable ((hM.isSemimartingale_of_bound hF hcM C hb).quadraticCovariation
      hA.isSemimartingale hF T) P ∧
      (∫ ω, (hM.isSemimartingale_of_bound hF hcM C hb).quadraticCovariation
        hA.isSemimartingale hF T ω ∂P) = 0 := by
  let τ : Ω → WithTop ℝ≥0 := fun _ ↦ T
  have hτ : IsStoppingTime F τ := isStoppingTime_const F T
  have hMs : Martingale (stoppedProcess M τ) F P :=
    (hM.isReducingStoppingTime_const T).2.1
  have hcs : HasCadlagPaths (stoppedProcess M τ) P := hcM.stoppedProcess τ
  have hbs : ∀ᵐ ω ∂P, ∀ t, ‖stoppedProcess M τ t ω‖ ≤ C := by
    filter_upwards [hb] with ω hω t
    exact hω _
  let hSM := hM.isSemimartingale_of_bound hF hcM C hb
  have hs := hSM.quadraticCovariation_stoppedProcess_left hA.isSemimartingale hF hτ
  apply hA.integrable_terminal_and_integral_eq_zero hMs hcs C hC hbs
  filter_upwards [hs] with ω hω
  have he : (fun t : ℝ≥0 ↦
      (hMs.isSemimartingale_of_bound hF hcs C hbs).quadraticCovariation
        hA.isSemimartingale hF t ω) =ᶠ[atTop]
      fun _ ↦ hSM.quadraticCovariation hA.isSemimartingale hF T ω := by
    filter_upwards [eventually_ge_atTop T] with t ht
    change (hSM.stoppedProcess hF hτ).quadraticCovariation hA.isSemimartingale hF t ω = _
    rw [hω t]
    simp only [MeasureTheory.stoppedProcess, τ, ← WithTop.coe_min, min_eq_right ht,
      WithTop.untopA, WithTop.untopD_coe]
  exact tendsto_const_nhds.congr' he.symm

theorem IsNatural.integrable_quadraticCovariation
    {hF : F.IsUsual P} (hA : IsNatural A F P hF)
    (hM : Martingale M F P) (hcM : HasCadlagPaths M P) (C : ℝ) (hC : 0 ≤ C)
    (hb : ∀ᵐ ω ∂P, ∀ t, ‖M t ω‖ ≤ C) (T : ℝ≥0) :
    Integrable ((hM.isSemimartingale_of_bound hF hcM C hb).quadraticCovariation
      hA.isSemimartingale hF T) P :=
  (hA.integrable_quadraticCovariation_and_integral_eq_zero hM hcM C hC hb T).1

theorem IsNatural.integral_quadraticCovariation_eq_zero
    {hF : F.IsUsual P} (hA : IsNatural A F P hF)
    (hM : Martingale M F P) (hcM : HasCadlagPaths M P) (C : ℝ) (hC : 0 ≤ C)
    (hb : ∀ᵐ ω ∂P, ∀ t, ‖M t ω‖ ≤ C) (T : ℝ≥0) :
    (∫ ω, (hM.isSemimartingale_of_bound hF hcM C hb).quadraticCovariation
      hA.isSemimartingale hF T ω ∂P) = 0 :=
  (hA.integrable_quadraticCovariation_and_integral_eq_zero hM hcM C hC hb T).2

end ProbabilityTheory
