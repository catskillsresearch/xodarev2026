/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.FiniteVariation.IntegralRegularity
public import StochLean.Analysis.PathVariation.CadlagIntegrandJumpCorrection
public import StochLean.Probability.Process.Measurability.Progressive

/-! # Cadlag integrands against finite-variation processes

The pathwise Stieltjes integral already accepts a cadlag right-value
integrand.  Compact boundedness supplies local variation-measure
integrability, while adapted right-continuous paths supply strong
progressivity.  Consequently the resulting right-value integral is an
adapted cadlag finite-variation semimartingale.
-/

@[expose] public section

open MeasureTheory StochLean Set Filter
open scoped NNReal

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {F : Filtration ℝ≥0 mΩ}
  (X : ℝ≥0 → Ω → ℝ)
  (hv : ∀ ω, LocallyBoundedVariationOn (fun t ↦ X t ω) univ)
  (hr : ∀ ω, IsRightContinuousPath (fun t ↦ X t ω))
  {H : ℝ≥0 → Ω → ℝ}

/-- A progressively measurable cadlag process is pathwise integrable against
every locally finite variation measure on compact time intervals. -/
theorem integrableOn_variationStieltjes_of_progressive_cadlag
    (hHp : IsStronglyProgressive F H)
    (hHc : ∀ ω, IsCadlagPath (fun t ↦ H t ω))
    (T : ℝ≥0) (ω : Ω) :
    IntegrableOn (fun t ↦ H t ω) (Ioc 0 T)
      (totalVariationStieltjes (fun t ↦ X t ω) (hv ω) (hr ω)).measure := by
  exact (integrableOn_variationStieltjes_cadlag_and_leftLim
    (hv ω) (hr ω) (hHc ω) T).1

/-- Adapted cadlag paths are strongly progressive and hence define an adapted
right-value finite-variation integral. -/
theorem isStronglyProgressive_finiteVariationIntegral_of_cadlag
    (ha : Adapted F X) (hHa : Adapted F H)
    (hHc : ∀ ω, IsCadlagPath (fun t ↦ H t ω)) :
    IsStronglyProgressive F (finiteVariationIntegral X hv hr H) := by
  have hHas : StronglyAdapted F H := fun t ↦ (hHa t).stronglyMeasurable
  have hHp := hHas.isStronglyProgressive_of_rightContinuous
    (fun ω ↦ (hHc ω).1)
  have hIa := adapted_finiteVariationIntegral X hv hr ha hHp
  have hIas : StronglyAdapted F (finiteVariationIntegral X hv hr H) :=
    fun t ↦ (hIa t).stronglyMeasurable
  apply hIas.isStronglyProgressive_of_rightContinuous
  intro ω
  exact (isCadlagPath_pathStieltjesIntegral
    (fun T ↦ integrableOn_variationStieltjes_of_progressive_cadlag
      X hv hr hHp hHc T ω)).1

/-- The right-value Stieltjes integral of an adapted cadlag integrand against
an everywhere cadlag locally-FV realization is a semimartingale. -/
theorem isSemimartingale_finiteVariationIntegral_of_cadlag
    {P : Measure Ω} [IsFiniteMeasure P]
    (ha : Adapted F X) (hF : F.IsUsual P)
    (hHa : Adapted F H) (hHc : ∀ ω, IsCadlagPath (fun t ↦ H t ω)) :
    IsSemimartingale (finiteVariationIntegral X hv hr H) F P := by
  have hHas : StronglyAdapted F H := fun t ↦ (hHa t).stronglyMeasurable
  have hHp := hHas.isStronglyProgressive_of_rightContinuous
    (fun ω ↦ (hHc ω).1)
  exact isSemimartingale_finiteVariationIntegral ha hF hHp
    (Eventually.of_forall fun ω T ↦
      integrableOn_variationStieltjes_of_progressive_cadlag
        X hv hr hHp hHc T ω)

end ProbabilityTheory
