/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Brownian.LevyIncrementLaw
public import StochLean.Probability.Process.IndependentIncrements.Filtration
public import Mathlib.Probability.BrownianMotion.Basic

/-! # Levy's characterization of real Brownian motion

A continuous local martingale whose raw quadratic variation is time is a
Brownian motion in Mathlib's canonical sense. The raw bracket condition
forces the zero initial value. For the continuous bracket version this
initial condition is explicit; arbitrary initial shifts remain permitted
in the separate increment-law and past-independence theorems.
-/

@[expose] public section

open MeasureTheory
open scoped NNReal

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
  {F : Filtration ℝ≥0 mΩ} {X : ℝ≥0 → Ω → ℝ}

theorem IsContinuousLocalMartingale.hasIndepIncrements_of_bracket_eq_time
    (hM : IsContinuousLocalMartingale X F P) (hF : F.IsUsual P)
    (hq : Indistinguishable ((hM.isSemimartingale hF).continuousQuadraticVariation hF)
      (fun t _ ↦ (t : ℝ)) P) : HasIndepIncrements X P :=
  (hM.isSemimartingale hF).adapted.hasIndepIncrements_of_indep_comap
    (fun _ _ hst ↦ hM.indep_increment_past_of_bracket_eq_time hF hq hst)

theorem IsContinuousLocalMartingale.isBrownianReal_of_continuousBracket_eq_time
    (hM : IsContinuousLocalMartingale X F P) (hF : F.IsUsual P)
    (hq : Indistinguishable ((hM.isSemimartingale hF).continuousQuadraticVariation hF)
      (fun t _ ↦ (t : ℝ)) P) (h0 : ∀ᵐ ω ∂P, X 0 ω = 0) : IsBrownianReal X P := by
  have hlaw (t : ℝ≥0) : HasLaw (X t) (gaussianReal 0 t) P := by
    have h := hM.hasLaw_gaussian_increment_of_bracket_eq_time hF hq
      (show (0 : ℝ≥0) ≤ t from zero_le)
    simp only [tsub_zero] at h
    apply h.congr
    filter_upwards [h0] with ω hω
    simp [hω]
  exact ⟨HasIndepIncrements.isPreBrownianReal_of_hasLaw hlaw
    (hM.hasIndepIncrements_of_bracket_eq_time hF hq), hM.2⟩

theorem IsContinuousLocalMartingale.isBrownianReal_of_quadraticVariation_eq_time
    (hM : IsContinuousLocalMartingale X F P) (hF : F.IsUsual P)
    (hq : Indistinguishable ((hM.isSemimartingale hF).quadraticVariation hF)
      (fun t _ ↦ (t : ℝ)) P) : IsBrownianReal X P := by
  let hX := hM.isSemimartingale hF
  have h0 : ∀ᵐ ω ∂P, X 0 ω = 0 := by
    filter_upwards [hq.ae_eq 0, hX.quadraticVariation_zero_ae hF] with ω hqω hzero
    have hs : (X 0 ω) ^ 2 = 0 := by simpa only [NNReal.coe_zero] using hzero.symm.trans hqω
    exact sq_eq_zero_iff.mp hs
  apply hM.isBrownianReal_of_continuousBracket_eq_time hF ?_ h0
  filter_upwards [hX.continuousQuadraticVariation_eq_of_continuous hF hM.2, hq, h0]
    with ω hcω hqω h0ω t
  simpa only [h0ω, zero_pow (by decide : 2 ≠ 0), sub_zero, hqω t] using hcω t

end ProbabilityTheory
