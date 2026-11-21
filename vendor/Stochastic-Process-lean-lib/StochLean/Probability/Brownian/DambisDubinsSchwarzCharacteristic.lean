/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Brownian.DambisDubinsSchwarzPaths
public import StochLean.Probability.Process.TimeChange.BracketStopping
public import
  StochLean.Probability.Process.Semimartingale.StochasticExponential.CharacteristicStopping
public import StochLean.Probability.Independence.ConditionalCharacteristic
public import Mathlib.Probability.Distributions.Gaussian.Real

/-! # Conditional Gaussian increments at inverse quadratic-variation times

Bounded characteristic exponentials and AE-finite optional sampling give
the conditional characteristic function. The actual Gaussian law and
independence from the stopping-time past then follow from Fourier uniqueness.
No square-moment theorem or prior Brownian/time-changed martingale law is assumed.
-/

@[expose] public section

open MeasureTheory
open scoped NNReal

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsFiniteMeasure P]
  {F : Filtration ℝ≥0 mΩ} {X : ℝ≥0 → Ω → ℝ}

theorem IsContinuousLocalMartingale.condExp_characteristic_inverse_clock
    (hM : IsContinuousLocalMartingale X F P) (hF : F.IsUsual P)
    (hu : ∀ᵐ ω ∂P, Filter.Tendsto
      ((hM.isSemimartingale hF).quadraticVariation hF · ω) Filter.atTop Filter.atTop)
    {s t : ℝ≥0} (hst : s ≤ t) (u : ℝ) :
    let hS := hM.isSemimartingale hF
    let A := hS.continuousBracketClock hF
    let hτ := (hS.adapted_continuousBracketClock hF).isStoppingTime_clockInverseTime hF
      (Filter.Eventually.of_forall (hS.continuous_continuousBracketClock hF))
    P[fun ω ↦ Complex.exp (Complex.I * (u : ℂ) *
      ((stoppedValue X (clockInverseTime A t) ω - stoppedValue X (clockInverseTime A s) ω : ℝ) : ℂ))
        | (hτ s).measurableSpace] =ᵐ[P]
      fun _ ↦ Complex.exp (Complex.ofReal (-((1 / 2 : ℝ) * u ^ 2) * ((t : ℝ) - s))) := by
  let hS := hM.isSemimartingale hF
  let A := hS.continuousBracketClock hF
  have hτ := (hS.adapted_continuousBracketClock hF).isStoppingTime_clockInverseTime hF
    (Filter.Eventually.of_forall (hS.continuous_continuousBracketClock hF))
  have hU := hM.tendsto_continuousQuadraticVariation_of_raw hF hu
  have hfin := clockInverseTime_finite_ae (hS.continuousBracketClock_unbounded_of_tendsto hF hU)
  have hlevels := hS.stoppedValue_continuousQuadraticVariation_inverseClock hF hU
  exact hM.condExp_characteristic_at_stoppingTimes hF (hτ s) (hτ t)
    (Filter.Eventually.of_forall (clockInverseTime_monotone A hst))
    (hfin.mono fun _ h ↦ h t) t
    (Filter.Eventually.of_forall fun ω r ↦
      hS.stopped_continuousQuadraticVariation_inverseClock_le hF t r ω)
    s t (hlevels.ae_eq s) (hlevels.ae_eq t) u

theorem IsContinuousLocalMartingale.condExp_inverse_clock_increment_gaussian
    (hM : IsContinuousLocalMartingale X F P) (hF : F.IsUsual P)
    (hu : ∀ᵐ ω ∂P, Filter.Tendsto
      ((hM.isSemimartingale hF).quadraticVariation hF · ω) Filter.atTop Filter.atTop)
    {s t : ℝ≥0} (hst : s ≤ t) (u : ℝ) :
    let hS := hM.isSemimartingale hF
    let A := hS.continuousBracketClock hF
    let hτ := (hS.adapted_continuousBracketClock hF).isStoppingTime_clockInverseTime hF
      (Filter.Eventually.of_forall (hS.continuous_continuousBracketClock hF))
    P[fun ω ↦ Complex.exp (Complex.I * (u : ℂ) *
      ((stoppedValue X (clockInverseTime A t) ω - stoppedValue X (clockInverseTime A s) ω : ℝ) : ℂ))
        | (hτ s).measurableSpace] =ᵐ[P] fun _ ↦ charFun (gaussianReal 0 (t - s)) u := by
  have he : Complex.exp (Complex.ofReal (-((1 / 2 : ℝ) * u ^ 2) *
      ((t : ℝ) - (s : ℝ)))) = charFun (gaussianReal 0 (t - s)) u := by
    rw [charFun_gaussianReal]
    congr 1
    simp only [NNReal.coe_sub hst, Complex.ofReal_mul, Complex.ofReal_neg,
      Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_ofNat, Complex.ofReal_pow,
      Complex.ofReal_sub, Complex.ofReal_zero, mul_zero, zero_mul, zero_sub]
    ring
  exact (hM.condExp_characteristic_inverse_clock hF hu hst u).trans
    (Filter.Eventually.of_forall fun _ ↦ he)

theorem IsContinuousLocalMartingale.hasLaw_and_indep_inverse_clock_increment
    [IsProbabilityMeasure P] (hM : IsContinuousLocalMartingale X F P) (hF : F.IsUsual P)
    (hu : ∀ᵐ ω ∂P, Filter.Tendsto
      ((hM.isSemimartingale hF).quadraticVariation hF · ω) Filter.atTop Filter.atTop)
    {s t : ℝ≥0} (hst : s ≤ t) :
    let hS := hM.isSemimartingale hF
    let A := hS.continuousBracketClock hF
    let hτ := (hS.adapted_continuousBracketClock hF).isStoppingTime_clockInverseTime hF
      (Filter.Eventually.of_forall (hS.continuous_continuousBracketClock hF))
    HasLaw (fun ω ↦ stoppedValue X (clockInverseTime A t) ω -
      stoppedValue X (clockInverseTime A s) ω) (gaussianReal 0 (t - s)) P ∧
      Indep (hτ s).measurableSpace (MeasurableSpace.comap
        (fun ω ↦ stoppedValue X (clockInverseTime A t) ω -
          stoppedValue X (clockInverseTime A s) ω) inferInstance) P := by
  let hS := hM.isSemimartingale hF
  have hcA : HasContinuousPaths (hS.continuousBracketClock hF) P :=
    Filter.Eventually.of_forall (hS.continuous_continuousBracketClock hF)
  have hτ := (hS.adapted_continuousBracketClock hF).isStoppingTime_clockInverseTime hF hcA
  have haB := adapted_stoppedValue_clockInverseTime (hS.adapted_continuousBracketClock hF)
    hF hcA hM.2 hM.1.1
  have hmeas := (haB.measurable (i := t)).sub (haB.measurable (i := s))
  exact ⟨hasLaw_of_condExp_characteristic (hτ s).measurableSpace_le hmeas
      (hM.condExp_inverse_clock_increment_gaussian hF hu hst),
    indep_comap_of_condExp_characteristic (ν := gaussianReal 0 (t - s))
      (hτ s).measurableSpace_le hmeas (hM.condExp_inverse_clock_increment_gaussian hF hu hst)⟩

end ProbabilityTheory
