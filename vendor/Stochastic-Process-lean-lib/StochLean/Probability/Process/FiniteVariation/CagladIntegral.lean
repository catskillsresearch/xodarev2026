/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.FiniteVariation.IntegralRegularity
public import StochLean.Probability.Process.Path.CagladBounded

/-! # The source caglad class is pathwise integrable against finite variation

Pathwise compact bounds are derived from regularity, not assumed. No global
sample-uniform bound, expected variation or initial integrability is needed.
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

theorem integrableOn_variationStieltjes_of_progressive_caglad
    (hHp : IsStronglyProgressive F H) (hHc : ∀ ω, IsCagladPath (fun t ↦ H t ω))
    (T : ℝ≥0) (ω : Ω) :
    IntegrableOn (fun t ↦ H t ω) (Ioc 0 T)
      (totalVariationStieltjes (fun t ↦ X t ω) (hv ω) (hr ω)).measure := by
  have hm : Measurable (fun t : ℝ≥0 ↦ H (min t T) ω) := by
    exact ((hHp T).comp_measurable
      (((measurable_id.min measurable_const).subtype_mk
        (h := fun t : ℝ≥0 ↦ by change min t T ≤ T; exact min_le_right _ _)).prodMk
          measurable_const)).measurable
  obtain ⟨C, _, hC⟩ := (hHc ω).exists_norm_bound_Icc T
  have hi : IntegrableOn (fun t ↦ H (min t T) ω) (Ioc 0 T)
      (totalVariationStieltjes (fun t ↦ X t ω) (hv ω) (hr ω)).measure := by
    apply integrableOn_variationStieltjes_of_bounded hm (C := C)
    intro t ht
    rw [min_eq_left ht.2]
    exact hC t ⟨ht.1.le, ht.2⟩
  apply hi.congr
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
  rw [min_eq_left ht.2]

theorem integrableOn_variationStieltjes_of_adapted_caglad
    (hHa : Adapted F H) (hHc : ∀ ω, IsCagladPath (fun t ↦ H t ω))
    (T : ℝ≥0) (ω : Ω) :
    IntegrableOn (fun t ↦ H t ω) (Ioc 0 T)
      (totalVariationStieltjes (fun t ↦ X t ω) (hv ω) (hr ω)).measure := by
  have hHas : StronglyAdapted F H := fun t ↦ (hHa t).stronglyMeasurable
  exact integrableOn_variationStieltjes_of_progressive_caglad X hv hr
    (hHas.isStronglyProgressive_of_leftContinuous (fun ω ↦ (hHc ω).1)) hHc T ω

theorem isStronglyProgressive_finiteVariationIntegral_of_caglad (ha : Adapted F X)
    (hHa : Adapted F H) (hHc : ∀ ω, IsCagladPath (fun t ↦ H t ω)) :
    IsStronglyProgressive F (finiteVariationIntegral X hv hr H) := by
  have hHas : StronglyAdapted F H := fun t ↦ (hHa t).stronglyMeasurable
  have hHp := hHas.isStronglyProgressive_of_leftContinuous (fun ω ↦ (hHc ω).1)
  have hIa := adapted_finiteVariationIntegral X hv hr ha hHp
  have hIas : StronglyAdapted F (finiteVariationIntegral X hv hr H) :=
    fun t ↦ (hIa t).stronglyMeasurable
  apply hIas.isStronglyProgressive_of_rightContinuous
  intro ω
  exact (isCadlagPath_pathStieltjesIntegral
    (fun T ↦ integrableOn_variationStieltjes_of_progressive_caglad X hv hr hHp hHc T ω)).1

theorem isSemimartingale_finiteVariationIntegral_of_caglad {P : Measure Ω} [IsFiniteMeasure P]
    (ha : Adapted F X) (hF : F.IsUsual P)
    (hHa : Adapted F H) (hHc : ∀ ω, IsCagladPath (fun t ↦ H t ω)) :
    IsSemimartingale (finiteVariationIntegral X hv hr H) F P := by
  have hHas : StronglyAdapted F H := fun t ↦ (hHa t).stronglyMeasurable
  have hHp := hHas.isStronglyProgressive_of_leftContinuous (fun ω ↦ (hHc ω).1)
  exact isSemimartingale_finiteVariationIntegral ha hF hHp
    (Eventually.of_forall fun ω T ↦
      integrableOn_variationStieltjes_of_progressive_caglad X hv hr hHp hHc T ω)

end ProbabilityTheory
