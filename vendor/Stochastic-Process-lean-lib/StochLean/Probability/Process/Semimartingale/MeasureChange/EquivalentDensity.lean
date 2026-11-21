/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.Semimartingale.MeasureChange.DensityProcess
public import Mathlib.MeasureTheory.Function.ConditionalExpectation.RadonNikodym

/-! # Strict positivity of density processes under equivalent measures

If two probability measures are mutually absolutely continuous, the terminal
Radon--Nikodym density is strictly positive almost surely.  Conditional
expectation preserves almost-sure strict positivity for integrable real
functions, so every fixed-time coordinate of the canonical density process is
strictly positive almost surely under the usual conditions.

The last assertion is deliberately coordinatewise in time.  This file does
not claim strict positivity at every real time on one common full-measure
event, define an inverse density process, or state a Girsanov theorem.
-/

@[expose] public section

open MeasureTheory Filter Set
open scoped ENNReal NNReal

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

/-- The conditional expectation of an integrable, almost surely strictly
positive real function is almost surely strictly positive with respect to any
sub-sigma-field. -/
theorem condExp_pos_ae_of_pos {P : Measure Ω} [IsProbabilityMeasure P]
    {m : MeasurableSpace Ω} (hm : m ≤ mΩ) {f : Ω → ℝ} (hf : Integrable f P)
    (hf_pos : ∀ᵐ ω ∂P, 0 < f ω) : ∀ᵐ ω ∂P, 0 < P[f | m] ω := by
  let z : Set Ω := {ω | P[f | m] ω = 0}
  have hz_meas : MeasurableSet[m] z := by
    exact stronglyMeasurable_condExp.measurable (measurableSet_singleton 0)
  have hf_nonneg : 0 ≤ᵐ[P] f := hf_pos.mono fun _ hω ↦ hω.le
  have hcond_nonneg : 0 ≤ᵐ[P] P[f | m] := condExp_nonneg hf_nonneg
  have hz_integral : (∫ ω in z, f ω ∂P) = 0 := by
    rw [← setIntegral_condExp (m := m) (m₀ := mΩ) (μ := P) hm hf hz_meas]
    exact integral_eq_zero_of_ae (by
      filter_upwards [ae_restrict_mem (hm z hz_meas)] with ω hω
      change P[f | m] ω = 0 at hω
      exact hω)
  have hf_zero : f =ᵐ[P.restrict z] 0 :=
    (setIntegral_eq_zero_iff_of_nonneg_ae
      (ae_mono Measure.restrict_le_self hf_nonneg) hf.integrableOn).mp hz_integral
  have hz_null : P z = 0 := by
    rw [← ae_restrict_eq_bot]
    rw [← empty_mem_iff_bot]
    change ∀ᵐ _ ∂P.restrict z, False
    filter_upwards [ae_mono Measure.restrict_le_self hf_pos, hf_zero] with ω hω hω_zero
    exact (ne_of_gt hω) hω_zero
  filter_upwards [hcond_nonneg, measure_eq_zero_iff_ae_notMem.mp hz_null] with ω hω hωz
  have hω_ne : P[f | m] ω ≠ 0 := by
    intro hzero
    apply hωz
    exact hzero
  exact lt_of_le_of_ne hω hω_ne.symm

variable {P Q : Measure Ω} [IsProbabilityMeasure P] [IsProbabilityMeasure Q]

/-- Under absolute continuity, the real terminal density of `Q` with respect
to `P` is strictly positive `Q`-almost surely. -/
theorem terminalDensity_pos_ae (hQP : Q ≪ P) :
    ∀ᵐ ω ∂Q, 0 < terminalDensity Q P ω := by
  filter_upwards [Measure.rnDeriv_pos hQP,
      hQP.ae_le (Measure.rnDeriv_ne_top Q P)]
    with ω hω_pos hω_top
  exact ENNReal.toReal_pos hω_pos.ne' hω_top

/-- Under equivalence, the terminal density is also strictly positive under
the source measure `P`. -/
theorem terminalDensity_pos_ae_under_source (hQP : Q ≪ P) (hPQ : P ≪ Q) :
    ∀ᵐ ω ∂P, 0 < terminalDensity Q P ω :=
  hPQ.ae_le (terminalDensity_pos_ae hQP)

variable {F : Filtration ℝ≥0 mΩ}

/-- Under absolute continuity, each fixed-time coordinate of the canonical
density process is strictly positive `Q`-almost surely. -/
theorem densityProcess_pos_ae (hQP : Q ≪ P) (hF : F.IsUsual P) (t : ℝ≥0) :
    ∀ᵐ ω ∂Q, 0 < densityProcess Q P F t ω := by
  let hm : F t ≤ mΩ := F.le t
  have htrim : Q.trim hm ≪ P.trim hm := hQP.trim hm
  have hderiv_pos :
      ∀ᵐ ω ∂Q.trim hm, 0 < ((Q.trim hm).rnDeriv (P.trim hm) ω).toReal := by
    filter_upwards [Measure.rnDeriv_pos htrim,
        htrim.ae_le (Measure.rnDeriv_ne_top (Q.trim hm) (P.trim hm))]
      with ω hω_pos hω_top
    exact ENNReal.toReal_pos hω_pos.ne' hω_top
  have hderiv_cond :
      (fun ω ↦ ((Q.trim hm).rnDeriv (P.trim hm) ω).toReal) =ᵐ[Q.trim hm]
        P[terminalDensity Q P | F t] :=
    htrim.ae_le (toReal_rnDeriv_trim hm hQP)
  have hcond_pos_trim : ∀ᵐ ω ∂Q.trim hm, 0 < P[terminalDensity Q P | F t] ω := by
    filter_upwards [hderiv_pos, hderiv_cond] with ω hω_pos hω_eq
    rwa [← hω_eq]
  have hcond_pos : ∀ᵐ ω ∂Q, 0 < P[terminalDensity Q P | F t] ω :=
    ae_of_ae_trim hm hcond_pos_trim
  filter_upwards [hQP.ae_le (densityProcess_ae_eq_condExp (Q := Q) hF t), hcond_pos]
    with ω hω hω_pos
  rwa [hω]

/-- Under equivalence of probability measures, each fixed-time coordinate of
the canonical density process is strictly positive `P`-almost surely. -/
theorem densityProcess_pos_ae_under_source (hQP : Q ≪ P) (hPQ : P ≪ Q)
    (hF : F.IsUsual P) (t : ℝ≥0) :
    ∀ᵐ ω ∂P, 0 < densityProcess Q P F t ω := by
  have hcond : ∀ᵐ ω ∂P, 0 < P[terminalDensity Q P | F t] ω :=
    condExp_pos_ae_of_pos (mΩ := mΩ) (P := P) (m := F t)
      (f := terminalDensity Q P) (F.le t) (integrable_terminalDensity Q P)
      (terminalDensity_pos_ae_under_source hQP hPQ)
  filter_upwards [densityProcess_ae_eq_condExp (Q := Q) hF t, hcond]
    with ω hω hω_pos
  rwa [hω]

/-- Under equivalence of probability measures, each fixed-time density is
nonzero `P`-almost surely. -/
theorem densityProcess_ne_zero_ae (hQP : Q ≪ P) (hPQ : P ≪ Q)
    (hF : F.IsUsual P) (t : ℝ≥0) :
    ∀ᵐ ω ∂P, densityProcess Q P F t ω ≠ 0 :=
  (densityProcess_pos_ae_under_source hQP hPQ hF t).mono fun _ hω ↦ hω.ne'

end ProbabilityTheory
