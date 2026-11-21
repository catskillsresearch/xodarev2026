/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import Mathlib.Probability.Process.Stopping

/-! # Commuting conditional expectations at stopping times

The stopping sigma-fields commute because their restrictions are ordered on
the two events comparing the stopping times. This proves Protter I.18's second
corollary directly for the native stopping owner, including infinite times.
No path regularization or additional ambient-terminal convention is required.
-/

@[expose] public section

open ProbabilityTheory Filter Set

namespace MeasureTheory

variable {Ω ι E : Type*} {mΩ : MeasurableSpace Ω}
  [LinearOrder ι] [TopologicalSpace ι] [OrderTopology ι] [SecondCountableTopology ι]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {P : Measure Ω} [IsFiniteMeasure P] {F : Filtration ι mΩ}
  {σ τ : Ω → WithTop ι} {Y : Ω → E}

private theorem condExp_stoppingTime_restrict_le_of_stronglyMeasurable
    (hσ : IsStoppingTime F σ) (hτ : IsStoppingTime F τ)
    (hi : Integrable Y P) (hm : StronglyMeasurable[hτ.measurableSpace] Y) :
    P[Y | hσ.measurableSpace] =ᵐ[P.restrict {ω | τ ω ≤ σ ω}] Y := by
  have hevent := hτ.measurableSet_le_stopping_time hσ
  rw [ae_eq_restrict_iff_indicator_ae_eq (hτ.measurableSpace_le _ hevent)]
  refine (condExp_indicator hi (hτ.measurableSet_stopping_time_le hσ)).symm.trans ?_
  have hmi : StronglyMeasurable[hσ.measurableSpace]
      ({ω | τ ω ≤ σ ω}.indicator Y) := by
    refine StronglyMeasurable.stronglyMeasurable_of_measurableSpace_le_on hevent ?_
      (hm.indicator hevent) ?_
    · intro A hA
      rw [Set.inter_comm _ A] at hA ⊢
      rw [hτ.measurableSet_inter_le_iff hσ, IsStoppingTime.measurableSet_min_iff hτ hσ] at hA
      exact hA.2
    · intro ω hω
      exact Set.indicator_of_notMem hω _
  exact condExp_of_aestronglyMeasurable' hσ.measurableSpace_le hmi.aestronglyMeasurable
    (hi.indicator (hτ.measurableSpace_le _ hevent))

/-- Conditioning a stopping-measurable variable at another stopping time
depends only on the earlier of the two times. -/
theorem condExp_stoppingTime_eq_min_of_stronglyMeasurable
    (hσ : IsStoppingTime F σ) (hτ : IsStoppingTime F τ)
    (hi : Integrable Y P) (hm : StronglyMeasurable[hτ.measurableSpace] Y) :
    P[Y | hσ.measurableSpace] =ᵐ[P] P[Y | (hσ.min hτ).measurableSpace] := by
  apply ae_of_ae_restrict_of_ae_restrict_compl {ω | σ ω ≤ τ ω}
  · exact (condExp_min_stopping_time_ae_eq_restrict_le hσ hτ).symm
  · have heq : P[Y | hσ.measurableSpace] =ᵐ[P.restrict {ω | τ ω ≤ σ ω}]
        P[Y | (hσ.min hτ).measurableSpace] := by
      refine (condExp_stoppingTime_restrict_le_of_stronglyMeasurable hσ hτ hi hm).trans ?_
      have h := condExp_min_stopping_time_ae_eq_restrict_le (f := Y) (μ := P) hτ hσ
      rw [condExp_of_stronglyMeasurable hτ.measurableSpace_le hm hi,
        hτ.measurableSpace_min hσ, inf_comm, ← hσ.measurableSpace_min hτ] at h
      exact h.symm
    rw [ae_restrict_iff'
      (hσ.measurableSpace_le _ (hσ.measurableSet_le_stopping_time hτ).compl)]
    rw [Filter.EventuallyEq, ae_restrict_iff'
      (hτ.measurableSpace_le _ (hτ.measurableSet_le_stopping_time hσ))] at heq
    filter_upwards [heq] with ω hω hmem
    exact hω (le_of_not_ge hmem)

theorem condExp_condExp_stoppingTime_eq_min
    (hσ : IsStoppingTime F σ) (hτ : IsStoppingTime F τ) :
    P[P[Y | hτ.measurableSpace] | hσ.measurableSpace] =ᵐ[P]
      P[Y | (hσ.min hτ).measurableSpace] :=
  (condExp_stoppingTime_eq_min_of_stronglyMeasurable hσ hτ
    integrable_condExp stronglyMeasurable_condExp).trans
      (condExp_condExp_of_le ((hσ.min hτ).measurableSpace_mono hτ
        (fun _ ↦ min_le_right _ _)) hτ.measurableSpace_le)

theorem condExp_stoppingTime_comm
    (hσ : IsStoppingTime F σ) (hτ : IsStoppingTime F τ) :
    P[P[Y | hτ.measurableSpace] | hσ.measurableSpace] =ᵐ[P]
      P[P[Y | hσ.measurableSpace] | hτ.measurableSpace] := by
  have h := condExp_condExp_stoppingTime_eq_min (Y := Y) (P := P) hτ hσ
  rw [hτ.measurableSpace_min hσ, inf_comm, ← hσ.measurableSpace_min hτ] at h
  exact (condExp_condExp_stoppingTime_eq_min hσ hτ).trans h.symm

end MeasureTheory
