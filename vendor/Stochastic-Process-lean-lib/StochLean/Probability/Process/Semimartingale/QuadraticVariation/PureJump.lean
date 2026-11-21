/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.Semimartingale.QuadraticVariation.FiniteVariation
public import StochLean.Probability.Process.Semimartingale.QuadraticVariation.ContinuousPartStopping
public import StochLean.Probability.Process.Semimartingale.QuadraticVariation.ContinuousPartAlgebra

/-! # Quadratic pure-jump semimartingales

This is a property of the existing semimartingale and its sole continuous
bracket, not a competing process or bracket owner. Quadratic pure jump does
not mean a process is constant between jumps: continuous FV drift qualifies.
-/

@[expose] public section

open MeasureTheory Set
open scoped NNReal

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsFiniteMeasure P]
  {F : Filtration ℝ≥0 mΩ} {X Y : ℝ≥0 → Ω → ℝ}

def IsSemimartingale.IsQuadraticPureJump
    (hX : IsSemimartingale X F P) (hF : F.IsUsual P) : Prop :=
  Indistinguishable (hX.continuousQuadraticVariation hF) 0 P

theorem IsSemimartingale.isQuadraticPureJump_iff_jump_decomposition
    (hX : IsSemimartingale X F P) (hF : F.IsUsual P) :
    hX.IsQuadraticPureJump hF ↔ Indistinguishable (hX.quadraticVariation hF)
      (fun t ω ↦ (X 0 ω) ^ 2 + ∑' s : Ioc 0 t, (jumpProcess X s ω) ^ 2) P := by
  constructor
  · intro h0
    filter_upwards [hX.quadraticVariation_continuous_jump_decomposition hF, h0] with ω hd hz t
    simpa only [hz t, Pi.zero_apply, add_zero] using (hd t).2
  · intro hq
    filter_upwards [hX.quadraticVariation_continuous_jump_decomposition hF, hq] with ω hd hqω t
    change hX.continuousQuadraticVariation hF t ω = 0
    linarith [(hd t).2, hqω t]

theorem IsSemimartingale.isQuadraticPureJump_of_finiteVariation
    (hX : IsSemimartingale X F P) (hF : F.IsUsual P) (hv : HasFiniteVariationPaths X P) :
    hX.IsQuadraticPureJump hF := hX.continuousQuadraticVariation_zero_of_finiteVariation hF hv

theorem IsSemimartingale.IsQuadraticPureJump.congr
    {hX : IsSemimartingale X F P} {hY : IsSemimartingale Y F P} {hF : F.IsUsual P}
    (hQ : hX.IsQuadraticPureJump hF) (he : Indistinguishable X Y P) :
    hY.IsQuadraticPureJump hF :=
  (hX.continuousQuadraticVariation_congr hY hF he).symm.trans hQ

theorem IsSemimartingale.IsQuadraticPureJump.stoppedProcess
    {hX : IsSemimartingale X F P} {hF : F.IsUsual P}
    (hQ : hX.IsQuadraticPureJump hF) {τ : Ω → WithTop ℝ≥0} (hτ : IsStoppingTime F τ) :
    (hX.stoppedProcess hF hτ).IsQuadraticPureJump hF := by
  have he : Indistinguishable (hX.continuousQuadraticVariation hF) 0 P := hQ
  filter_upwards [hX.continuousQuadraticVariation_stoppedProcess hF hτ,
    he.stoppedProcess τ] with ω hs h0 t
  exact (hs t).trans (h0 t)

theorem IsSemimartingale.isQuadraticPureJump_iff_raw_constant_of_continuous
    (hX : IsSemimartingale X F P) (hF : F.IsUsual P) (hc : HasContinuousPaths X P) :
    hX.IsQuadraticPureJump hF ↔
      Indistinguishable (hX.quadraticVariation hF) (fun _ ω ↦ (X 0 ω) ^ 2) P := by
  constructor
  · intro h0
    filter_upwards [hX.continuousQuadraticVariation_eq_of_continuous hF hc, h0]
      with ω he hz t
    have h := he t
    rw [hz t] at h
    exact (sub_eq_zero.mp h.symm)
  · intro hq
    filter_upwards [hX.continuousQuadraticVariation_eq_of_continuous hF hc, hq]
      with ω he hqω t
    rw [he t, hqω t, sub_self]
    rfl

end ProbabilityTheory
