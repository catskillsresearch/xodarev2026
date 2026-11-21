/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Martingale.Convergence.Regularization
public import StochLean.Probability.Process.Path.RightContinuousOrder
public import Mathlib.MeasureTheory.Measure.Decomposition.IntegralRNDeriv
public import Mathlib.Probability.Process.Filtration

/-! # Density processes for absolutely continuous probability measures

For probability measures `Q ≪ P`, the terminal density is the real-valued
Radon--Nikodym derivative of `Q` with respect to `P`.  Its conditional
expectations form a uniformly integrable `P`-martingale.  Under the usual
conditions, the canonical dyadic right-limit construction supplies its
cadlag version.

This file owns only the density-process foundation.  It does not assert a
Girsanov decomposition, strict positivity, an inverse density, or a value at
time zero.  In particular, no triviality assumption on the initial sigma-field
is hidden in the construction.
-/

@[expose] public section

open MeasureTheory Filter Set
open scoped NNReal ENNReal

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

/-- The real terminal Radon--Nikodym density of `Q` with respect to `P`. -/
noncomputable def terminalDensity (Q P : Measure Ω) : Ω → ℝ :=
  fun ω ↦ (Q.rnDeriv P ω).toReal

/-- The terminal density is measurable for the ambient measurable space. -/
theorem measurable_terminalDensity (Q P : Measure Ω) : Measurable (terminalDensity Q P) :=
  (Q.measurable_rnDeriv P).ennreal_toReal

/-- The real terminal density is pointwise nonnegative. -/
theorem terminalDensity_nonneg (Q P : Measure Ω) (ω : Ω) :
    0 ≤ terminalDensity Q P ω :=
  ENNReal.toReal_nonneg

/-- A finite measure has an integrable real Radon--Nikodym density. -/
theorem integrable_terminalDensity (Q P : Measure Ω) [IsFiniteMeasure Q] :
    Integrable (terminalDensity Q P) P :=
  Measure.integrable_toReal_rnDeriv

variable {P Q : Measure Ω} [IsProbabilityMeasure P] [IsProbabilityMeasure Q]

/-- Integration of the terminal density over any set recovers the real mass
of that set under the absolutely continuous measure. -/
theorem setIntegral_terminalDensity (hQP : Q ≪ P) (s : Set Ω) :
    (∫ ω in s, terminalDensity Q P ω ∂P) = Q.real s := by
  exact Measure.setIntegral_toReal_rnDeriv hQP s

/-- The terminal density has total integral one. -/
theorem integral_terminalDensity (hQP : Q ≪ P) :
    (∫ ω, terminalDensity Q P ω ∂P) = 1 := by
  simpa only [terminalDensity, probReal_univ] using
    (Measure.integral_toReal_rnDeriv hQP)

/-- The canonical cadlag density process is the dyadic right-limit
regularization of the conditional-expectation martingale. -/
noncomputable def densityProcess (Q P : Measure Ω) (F : Filtration ℝ≥0 mΩ) :
    ℝ≥0 → Ω → ℝ :=
  dyadicRightLimitProcess (fun t ↦ P[terminalDensity Q P | F t])

variable {F : Filtration ℝ≥0 mΩ}

omit [IsProbabilityMeasure Q] in
private theorem densityProcess_isModification (hF : F.IsUsual P) :
    IsModification (fun t ↦ P[terminalDensity Q P | F t]) (densityProcess Q P F) P := by
  let hM : Martingale (fun t ↦ P[terminalDensity Q P | F t]) F P :=
    martingale_condExp (terminalDensity Q P) F P
  simpa only [densityProcess] using
    hM.supermartingale.isModification_dyadicRightLimitProcess hF
      hM.isRightContinuousPath_integral

omit [IsProbabilityMeasure Q] in
/-- At every time, the canonical process agrees almost surely with the
corresponding conditional expectation of the terminal density. -/
theorem densityProcess_ae_eq_condExp (hF : F.IsUsual P) (t : ℝ≥0) :
    densityProcess Q P F t =ᵐ[P] P[terminalDensity Q P | F t] :=
  (densityProcess_isModification (Q := Q) hF t).symm

omit [IsProbabilityMeasure Q] in
/-- The canonical density process is a true `P`-martingale. -/
theorem martingale_densityProcess (hF : F.IsUsual P) :
    Martingale (densityProcess Q P F) F P := by
  let hM : Martingale (fun t ↦ P[terminalDensity Q P | F t]) F P :=
    martingale_condExp (terminalDensity Q P) F P
  exact hM.congr
    (hM.supermartingale.stronglyAdapted_dyadicRightLimitProcess hF)
    (densityProcess_isModification (Q := Q) hF)

omit [IsProbabilityMeasure Q] in
/-- The canonical density process has cadlag paths on one common full-measure
event. -/
theorem hasCadlagPaths_densityProcess : HasCadlagPaths (densityProcess Q P F) P := by
  let hM : Martingale (fun t ↦ P[terminalDensity Q P | F t]) F P :=
    martingale_condExp (terminalDensity Q P) F P
  simpa only [densityProcess] using
    hM.supermartingale.hasCadlagPaths_dyadicRightLimitProcess

/-- The canonical density process is uniformly integrable. -/
theorem uniformIntegrable_densityProcess (hF : F.IsUsual P) :
    UniformIntegrable (densityProcess Q P F) 1 P := by
  have hUI : UniformIntegrable (fun t ↦ P[terminalDensity Q P | F t]) 1 P :=
    (integrable_terminalDensity Q P).uniformIntegrable_condExp_filtration
  exact hUI.ae_eq fun t ↦ (densityProcess_ae_eq_condExp (Q := Q) hF t).symm

omit [IsProbabilityMeasure Q] in
/-- Nonnegativity holds simultaneously at every time on one full-measure
event.  Right continuity is essential for passing from coordinatewise almost
sure inequalities to this conclusion. -/
theorem ae_forall_densityProcess_nonneg (hF : F.IsUsual P) :
    ∀ᵐ ω ∂P, ∀ t : ℝ≥0, 0 ≤ densityProcess Q P F t ω := by
  have hz : HasRightContinuousPaths (fun _ : ℝ≥0 ↦ (0 : Ω → ℝ)) P :=
    Eventually.of_forall fun _ _ ↦ continuousWithinAt_const
  apply hz.ae_forall_le_of_forall_ae_le
    (hasCadlagPaths_densityProcess (P := P) (Q := Q) (F := F)).hasRightContinuousPaths
  intro t
  exact (condExp_nonneg (Eventually.of_forall (terminalDensity_nonneg Q P))).trans_eq
    (densityProcess_ae_eq_condExp (Q := Q) hF t).symm

/-- On every event measurable at time `t`, integrating the canonical density
process against `P` gives that event's real `Q`-mass. -/
theorem setIntegral_densityProcess (hQP : Q ≪ P) (hF : F.IsUsual P)
    (t : ℝ≥0) {s : Set Ω} (hs : MeasurableSet[F t] s) :
    (∫ ω in s, densityProcess Q P F t ω ∂P) = Q.real s := by
  calc
    (∫ ω in s, densityProcess Q P F t ω ∂P) =
        ∫ ω in s, P[terminalDensity Q P | F t] ω ∂P :=
      setIntegral_congr_ae (F.le t s hs) (by
        filter_upwards [densityProcess_ae_eq_condExp (Q := Q) hF t] with ω hω _
        exact hω)
    _ = ∫ ω in s, terminalDensity Q P ω ∂P :=
      setIntegral_condExp (F.le t) (integrable_terminalDensity Q P) hs
    _ = Q.real s := setIntegral_terminalDensity hQP s

end ProbabilityTheory
