/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.Semimartingale.MeasureChange.PathwiseReciprocal
public import StochLean.Probability.Martingale.OptionalSampling.ContinuousClosingTerminal
public import StochLean.Probability.Process.Path.Stopping
public import StochLean.Probability.Process.Stopping.Finite

/-! # Density processes at finite stopping times

The canonical density sampled at an everywhere finite stopping time is the
conditional expectation of the terminal Radon--Nikodym density on the native
stopping sigma-field.  Consequently it integrates to the target measure on
every stopping-time event.  Under absolute continuity it is strictly positive
under the target law; under equivalence the source-law and reciprocal
statements follow as well.

No localization of semimartingales or Girsanov decomposition is asserted here.
-/

@[expose] public section

open MeasureTheory Filter Set
open scoped ENNReal NNReal

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}
  {P Q : Measure Ω} [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
  {F : Filtration ℝ≥0 mΩ}

/-- Conditional expectation of a terminal density onto any sub-sigma-field is
strictly positive under the target measure. -/
theorem condExp_terminalDensity_pos_ae (hQP : Q ≪ P)
    {m : MeasurableSpace Ω} (hm : m ≤ mΩ) :
    ∀ᵐ ω ∂Q, 0 < P[terminalDensity Q P | m] ω := by
  have htrim : Q.trim hm ≪ P.trim hm := hQP.trim hm
  have hderiv_pos :
      ∀ᵐ ω ∂Q.trim hm, 0 < ((Q.trim hm).rnDeriv (P.trim hm) ω).toReal := by
    filter_upwards [Measure.rnDeriv_pos htrim,
        htrim.ae_le (Measure.rnDeriv_ne_top (Q.trim hm) (P.trim hm))]
      with ω hω_pos hω_top
    exact ENNReal.toReal_pos hω_pos.ne' hω_top
  have hderiv_cond :
      (fun ω ↦ ((Q.trim hm).rnDeriv (P.trim hm) ω).toReal) =ᵐ[Q.trim hm]
        P[terminalDensity Q P | m] :=
    htrim.ae_le (toReal_rnDeriv_trim hm hQP)
  apply ae_of_ae_trim hm
  filter_upwards [hderiv_pos, hderiv_cond] with ω hω_pos hω_eq
  rwa [← hω_eq]

/-- At an everywhere finite stopping time, the canonical density is the
conditional expectation of the terminal density on the stopping sigma-field. -/
theorem densityProcess_sample_ae_eq_condExp_terminalDensity
    (hF : F.IsUsual P) (τ : FiniteStoppingTime F) :
    (fun ω ↦ densityProcess Q P F (τ ω) ω) =ᵐ[P]
      P[terminalDensity Q P | τ.measurableSpace] := by
  change (fun ω ↦ densityProcess Q P F (τ ω) ω) =ᵐ[P]
    P[terminalDensity Q P | τ.isStoppingTime.measurableSpace]
  have hsample :=
    MeasureTheory.Martingale.stoppedValue_closingProjection_ae_eq_condExp
      (martingale_densityProcess (Q := Q) hF)
      (hasCadlagPaths_densityProcess (P := P) (Q := Q) (F := F)).hasRightContinuousPaths
      hF (integrable_terminalDensity Q P)
      (densityProcess_ae_eq_condExp (Q := Q) hF) τ.isStoppingTime
  simpa only [FiniteStoppingTime.withTop, stoppedValueWithTerminal_coe] using hsample

/-- The density sampled at an everywhere finite stopping time is integrable
under the source measure. -/
theorem integrable_densityProcess_sample (hF : F.IsUsual P)
    (τ : FiniteStoppingTime F) :
    Integrable (fun ω ↦ densityProcess Q P F (τ ω) ω) P :=
  integrable_condExp.congr
    (densityProcess_sample_ae_eq_condExp_terminalDensity (Q := Q) hF τ).symm

/-- Integrating the sampled density on a stopping-time event recovers its
target-law probability. -/
theorem setIntegral_densityProcess_sample (hQP : Q ≪ P) (hF : F.IsUsual P)
    (τ : FiniteStoppingTime F) {s : Set Ω}
    (hs : MeasurableSet[τ.measurableSpace] s) :
    (∫ ω in s, densityProcess Q P F (τ ω) ω ∂P) = Q.real s := by
  calc
    (∫ ω in s, densityProcess Q P F (τ ω) ω ∂P) =
        ∫ ω in s, P[terminalDensity Q P | τ.measurableSpace] ω ∂P :=
      setIntegral_congr_ae (τ.measurableSpace_le s hs) (by
        filter_upwards
          [densityProcess_sample_ae_eq_condExp_terminalDensity (Q := Q) hF τ]
          with ω hω _
        exact hω)
    _ = ∫ ω in s, terminalDensity Q P ω ∂P :=
      setIntegral_condExp τ.measurableSpace_le (integrable_terminalDensity Q P) hs
    _ = Q.real s := setIntegral_terminalDensity hQP s

/-- Under one-way absolute continuity, a finite-stopping-time density sample is
strictly positive under the target law. -/
theorem densityProcess_sample_pos_ae (hQP : Q ≪ P) (hF : F.IsUsual P)
    (τ : FiniteStoppingTime F) :
    ∀ᵐ ω ∂Q, 0 < densityProcess Q P F (τ ω) ω := by
  filter_upwards
      [hQP.ae_le (densityProcess_sample_ae_eq_condExp_terminalDensity (Q := Q) hF τ),
        condExp_terminalDensity_pos_ae hQP τ.measurableSpace_le]
    with ω hω hω_pos
  rwa [hω]

/-- Under equivalence, a finite-stopping-time density sample is also strictly
positive under the source law. -/
theorem densityProcess_sample_pos_ae_under_source
    (hQP : Q ≪ P) (hPQ : P ≪ Q) (hF : F.IsUsual P)
    (τ : FiniteStoppingTime F) :
    ∀ᵐ ω ∂P, 0 < densityProcess Q P F (τ ω) ω :=
  hPQ.ae_le (densityProcess_sample_pos_ae hQP hF τ)

/-- At an everywhere finite stopping time, the reverse density sample is the
reciprocal of the forward density sample under the source law. -/
theorem densityProcess_reverse_sample_ae_eq_inv
    (hQP : Q ≪ P) (hPQ : P ≪ Q) (hF : F.IsUsual P)
    (τ : FiniteStoppingTime F) :
    (fun ω ↦ densityProcess P Q F (τ ω) ω) =ᵐ[P]
      fun ω ↦ 1 / densityProcess Q P F (τ ω) ω := by
  have hsample :=
    (inverse_densityProcess_indistinguishable_reverse hQP hPQ hF).stoppedValue τ.withTop
  simpa only [FiniteStoppingTime.withTop, FiniteStoppingTime.stoppedValue_eq]
    using hsample.symm

end ProbabilityTheory
