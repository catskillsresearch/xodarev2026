/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.Semimartingale.MeasureChange.ReciprocalBayes
public import StochLean.Probability.Process.Path.Multiplication

/-! # Pathwise reciprocal density processes

Under equivalent probability measures, the two canonical cadlag density
processes are reciprocals on one common full-measure event.  The upgrade from
fixed-time almost-sure equality uses uniqueness of right-continuous
modifications, not an uncountable intersection of coordinate null sets.

This file does not sample the identity at stopping times, construct
localizers, or state a Girsanov theorem.
-/

@[expose] public section

open MeasureTheory Filter
open scoped NNReal

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}
  {P Q : Measure Ω} [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
  {F : Filtration ℝ≥0 mΩ}

/-- Under equivalent laws, the reverse and forward canonical densities have
product one at every time on one common `P`-full-measure event. -/
theorem densityProcess_reverse_mul_indistinguishable_one
    (hQP : Q ≪ P) (hPQ : P ≪ Q) (hF : F.IsUsual P) :
    Indistinguishable
      (densityProcess P Q F * densityProcess Q P F)
      (fun _ _ ↦ (1 : ℝ)) P := by
  have hFQ : F.IsUsual Q := hF.of_absolutelyContinuous hPQ
  have hreverse_cadlag : HasCadlagPaths (densityProcess P Q F) P :=
    hPQ.ae_le (hasCadlagPaths_densityProcess (P := Q) (Q := P) (F := F))
  have hforward_cadlag : HasCadlagPaths (densityProcess Q P F) P :=
    hasCadlagPaths_densityProcess
  have hmod : IsModification
      (densityProcess P Q F * densityProcess Q P F)
      (fun _ _ ↦ (1 : ℝ)) P := by
    intro t
    filter_upwards [densityProcess_reverse_ae_eq_inv_under_source hQP hPQ hF t,
        densityProcess_pos_ae (P := Q) (Q := P) hPQ hFQ t]
      with ω hrecip hreverse_pos
    change densityProcess P Q F t ω * densityProcess Q P F t ω = 1
    rw [hrecip]
    simp only [one_div]
    exact mul_inv_cancel₀ hreverse_pos.ne'
  exact hmod.indistinguishable_of_rightContinuous
    (hreverse_cadlag.mul hforward_cadlag).hasRightContinuousPaths
    (Eventually.of_forall fun _ _ ↦ continuousWithinAt_const)

/-- Equivalent measures make the forward density strictly positive at every
time on one common `P`-full-measure event. -/
theorem ae_forall_densityProcess_pos_of_equivalent
    (hQP : Q ≪ P) (hPQ : P ≪ Q) (hF : F.IsUsual P) :
    ∀ᵐ ω ∂P, ∀ t : ℝ≥0, 0 < densityProcess Q P F t ω := by
  filter_upwards [densityProcess_reverse_mul_indistinguishable_one hQP hPQ hF,
      ae_forall_densityProcess_nonneg (Q := Q) hF]
    with ω hproduct hnonneg
  intro t
  have hne : densityProcess Q P F t ω ≠ 0 := by
    intro hzero
    have hone := hproduct t
    change densityProcess P Q F t ω * densityProcess Q P F t ω = 1 at hone
    rw [hzero, mul_zero] at hone
    exact zero_ne_one hone
  exact lt_of_le_of_ne (hnonneg t) hne.symm

/-- Equivalent measures make the forward density nonzero at every time on one
common `P`-full-measure event. -/
theorem ae_forall_densityProcess_ne_zero_of_equivalent
    (hQP : Q ≪ P) (hPQ : P ≪ Q) (hF : F.IsUsual P) :
    ∀ᵐ ω ∂P, ∀ t : ℝ≥0, densityProcess Q P F t ω ≠ 0 :=
  (ae_forall_densityProcess_pos_of_equivalent hQP hPQ hF).mono
    fun _ hω t ↦ (hω t).ne'

/-- The pointwise inverse of the forward density is indistinguishable from
the reverse canonical density under the source measure. -/
theorem inverse_densityProcess_indistinguishable_reverse
    (hQP : Q ≪ P) (hPQ : P ≪ Q) (hF : F.IsUsual P) :
    Indistinguishable
      (fun t ω ↦ 1 / densityProcess Q P F t ω)
      (densityProcess P Q F) P := by
  filter_upwards [densityProcess_reverse_mul_indistinguishable_one hQP hPQ hF,
      ae_forall_densityProcess_ne_zero_of_equivalent hQP hPQ hF]
    with ω hproduct hne
  intro t
  exact ((eq_div_iff (hne t)).2 (hproduct t)).symm

/-- The pathwise inverse density has cadlag paths under the source measure. -/
theorem hasCadlagPaths_inverse_densityProcess
    (hQP : Q ≪ P) (hPQ : P ≪ Q) (hF : F.IsUsual P) :
    HasCadlagPaths (fun t ω ↦ 1 / densityProcess Q P F t ω) P := by
  have hreverse : HasCadlagPaths (densityProcess P Q F) P :=
    hPQ.ae_le (hasCadlagPaths_densityProcess (P := Q) (Q := P) (F := F))
  exact hreverse.congr
    (inverse_densityProcess_indistinguishable_reverse hQP hPQ hF).symm

end ProbabilityTheory
