/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.ClassD.Local
public import StochLean.Probability.Process.ClassD.Stopping
public import StochLean.Probability.Martingale.OptionalSampling.ContinuousUniformIntegrable

/-! # Class D and Class DL for true martingales

For a right-continuous true martingale, UI at deterministic times is equivalent
to Class D. Every right-continuous true martingale is Class DL. These are proved
bridges using optional sampling, not definitions of the stopping-family owners.
-/

@[expose] public section

open ProbabilityTheory Filter
open scoped NNReal

namespace MeasureTheory.Martingale

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsFiniteMeasure P]
  {F : Filtration ℝ≥0 mΩ} {X : ℝ≥0 → Ω → ℝ}

theorem isClassD_iff_uniformIntegrable_of_progressive (hX : Martingale X F P)
    (hp : IsStronglyProgressive F X) (hr : HasRightContinuousPaths X P) :
    IsClassD X F P ↔ UniformIntegrable X 1 P := by
  refine ⟨fun h ↦ h.uniformIntegrable, fun hu ↦ ?_⟩
  exact hX.uniformIntegrable_stoppedValue_of_ae_finite_continuous hu hp hr
    (fun τ : FiniteStoppingTime F ↦ τ.isStoppingTime)
    (fun τ ↦ ae_of_all P τ.withTop_ne_top)

theorem isClassD_iff_uniformIntegrable_of_usual (hX : Martingale X F P)
    (hF : F.IsUsual P) (hr : HasRightContinuousPaths X P) :
    IsClassD X F P ↔ UniformIntegrable X 1 P := by
  refine ⟨fun h ↦ h.uniformIntegrable, fun hu ↦ ?_⟩
  exact hX.uniformIntegrable_stoppedValue_of_ae_finite_usual hu hF hr
    (fun τ : FiniteStoppingTime F ↦ τ.isStoppingTime)
    (fun τ ↦ ae_of_all P τ.withTop_ne_top)

theorem isClassDL_of_progressive (hX : Martingale X F P)
    (hp : IsStronglyProgressive F X) (hr : HasRightContinuousPaths X P) :
    IsClassDL X F P := by
  intro T
  apply ((hX.integrable T).uniformIntegrable_condExp
    (fun τ : {τ : FiniteStoppingTime F | ∀ ω, τ ω ≤ T} ↦ τ.1.measurableSpace_le)).ae_eq
  intro τ
  exact (hX.finiteStoppingTime_value_ae_eq_condExp_of_progressive hp hr τ.1 τ.2).symm

theorem isClassDL_of_usual (hX : Martingale X F P)
    (hF : F.IsUsual P) (hr : HasRightContinuousPaths X P) : IsClassDL X F P := by
  intro T
  apply ((hX.integrable T).uniformIntegrable_condExp
    (fun τ : {τ : FiniteStoppingTime F | ∀ ω, τ ω ≤ T} ↦ τ.1.measurableSpace_le)).ae_eq
  intro τ
  exact (hX.stoppedValue_ae_eq_condExp_of_bounded_usual hF hr τ.1.isStoppingTime
    (fun ω ↦ WithTop.coe_le_coe.mpr (τ.2 ω))).symm

end MeasureTheory.Martingale
