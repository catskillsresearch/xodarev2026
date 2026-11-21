/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Analysis.PathVariation.CadlagC1ChangeOfVariables
public import StochLean.Probability.Process.Semimartingale.FiniteVariation
public import StochLean.Probability.Process.Path.Algebra

/-! # Protter II.31 for cadlag finite-variation processes -/

@[expose] public section

open MeasureTheory StochLean Set
open scoped NNReal

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
  {X : ℝ≥0 → Ω → ℝ} {f : ℝ → ℝ}

theorem HasFiniteVariationPaths.hasCadlagPaths_of_rightContinuous
    (hv : HasFiniteVariationPaths X P) (hr : HasRightContinuousPaths X P) : HasCadlagPaths X P := by
  filter_upwards [hv, hr] with ω hvω hrω
  exact isCadlagPath_of_locallyBoundedVariation hvω hrω

theorem HasFiniteVariationPaths.contDiff_comp_of_cadlag (hv : HasFiniteVariationPaths X P)
    (hx : HasCadlagPaths X P) (hf : ContDiff ℝ 1 f) :
    HasFiniteVariationPaths (fun t ω ↦ f (X t ω)) P := by
  filter_upwards [hv, hx] with ω hvω hxω
  exact locallyBoundedVariationOn_contDiff_comp_of_cadlag hvω hxω hf

theorem HasFiniteVariationPaths.contDiff_comp_of_rightContinuous (hv : HasFiniteVariationPaths X P)
    (hr : HasRightContinuousPaths X P) (hf : ContDiff ℝ 1 f) :
    HasFiniteVariationPaths (fun t ω ↦ f (X t ω)) P :=
  hv.contDiff_comp_of_cadlag (hv.hasCadlagPaths_of_rightContinuous hr) hf

theorem isSemimartingale_contDiff_of_cadlag_finiteVariation
    {F : Filtration ℝ≥0 mΩ} [IsFiniteMeasure P] (ha : Adapted F X) (hF : F.IsUsual P)
    (hv : HasFiniteVariationPaths X P) (hx : HasCadlagPaths X P) (hf : ContDiff ℝ 1 f) :
    IsSemimartingale (fun t ω ↦ f (X t ω)) F P :=
  (hv.contDiff_comp_of_cadlag hx hf).isSemimartingale
    (fun t ↦ hf.continuous.measurable.comp (ha t)) hF (hx.continuous_comp hf.continuous)

theorem HasFiniteVariationPaths.contDiff_change_of_variables
    (hv : HasFiniteVariationPaths X P) (hx : HasCadlagPaths X P) (hf : ContDiff ℝ 1 f) :
    ∀ᵐ ω ∂P, ∃ hvω : LocallyBoundedVariationOn (X · ω) univ,
      ∃ hxω : IsCadlagPath (X · ω), ∀ t : ℝ≥0,
        Summable (fun s : Ioc 0 t ↦ |f (X s ω) - f (Function.leftLim (X · ω) s) -
          deriv f (Function.leftLim (X · ω) s) * (X s ω - Function.leftLim (X · ω) s)|) ∧
        f (X t ω) - f (X 0 ω) =
          pathStieltjesIncrementIntegral (X · ω) hvω hxω.1
            (fun s ↦ deriv f (Function.leftLim (X · ω) s)) 0 t +
            ∑' s : Ioc 0 t, (f (X s ω) - f (Function.leftLim (X · ω) s) -
              deriv f (Function.leftLim (X · ω) s) * (X s ω - Function.leftLim (X · ω) s)) := by
  filter_upwards [hv, hx] with ω hvω hxω
  exact ⟨hvω, hxω, fun t ↦ ⟨summable_abs_contDiff_jump_remainders hvω hxω hf t,
    pathStieltjesIncrementIntegral_contDiff_cadlag hvω hxω hf t⟩⟩

end ProbabilityTheory
