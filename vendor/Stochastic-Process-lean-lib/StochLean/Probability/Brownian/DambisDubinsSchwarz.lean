/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Brownian.DambisDubinsSchwarzCharacteristic
public import StochLean.Probability.Process.IndependentIncrements.Filtration
public import Mathlib.Probability.BrownianMotion.Basic

/-! # Dambis--Dubins--Schwarz: the Brownian law

The inverse of the canonical continuous bracket turns a continuous local
martingale starting at zero with unbounded bracket into a real Brownian motion.
Conditional characteristic functions give independence from the entire sampled
past, not just pairwise independence. Flat bracket intervals are permitted.
-/

@[expose] public section

open MeasureTheory Filter
open scoped NNReal

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
  {F : Filtration ℝ≥0 mΩ} {X : ℝ≥0 → Ω → ℝ}

theorem IsContinuousLocalMartingale.isBrownianReal_inverse_clock
    (hM : IsContinuousLocalMartingale X F P) (hF : F.IsUsual P)
    (h0 : X 0 =ᵐ[P] 0)
    (hu : ∀ᵐ ω ∂P, Tendsto
      ((hM.isSemimartingale hF).quadraticVariation hF · ω) atTop atTop) :
    IsBrownianReal (fun s ↦ stoppedValue X
      (clockInverseTime ((hM.isSemimartingale hF).continuousBracketClock hF) s)) P := by
  let hS := hM.isSemimartingale hF
  let A := hS.continuousBracketClock hF
  let B := fun s ↦ stoppedValue X (clockInverseTime A s)
  obtain ⟨hτ, _, hcB, haB, hrec, _, _⟩ := hM.inverse_quadraticVariation_timeChange hF hu
  have hind : HasIndepIncrements B P :=
    haB.hasIndepIncrements_of_indep_comap
      (fun _ _ hst ↦ (hM.hasLaw_and_indep_inverse_clock_increment hF hu hst).2)
  have hB0 : B 0 =ᵐ[P] 0 := by
    filter_upwards [hrec.ae_eq 0, h0] with ω hr hω
    simpa only [hS.continuousBracketClock_zero hF, hω] using hr
  have hlaw (t : ℝ≥0) : HasLaw (B t) (gaussianReal 0 t) P := by
    have h := (hM.hasLaw_and_indep_inverse_clock_increment hF hu
      (show (0 : ℝ≥0) ≤ t from zero_le)).1
    simp only [tsub_zero] at h
    apply h.congr
    filter_upwards [hB0] with ω hω
    change B t ω = B t ω - B 0 ω
    simp only [hω, Pi.zero_apply, sub_zero]
  exact ⟨HasIndepIncrements.isPreBrownianReal_of_hasLaw hlaw hind, hcB⟩

end ProbabilityTheory
