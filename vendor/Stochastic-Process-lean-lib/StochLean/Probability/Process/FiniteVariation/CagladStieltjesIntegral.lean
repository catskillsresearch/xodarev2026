/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.FiniteVariation.CagladIntegral
public import StochLean.Analysis.PathVariation.StieltjesIntegralDecomposition

/-! # Deterministic caglad integrands for the original increasing-path integral

Pathwise integrability follows from the existing progressive caglad result on
the one-point sample space. No random uniform bound or moment is imposed.
-/

@[expose] public section

open MeasureTheory StochLean Set
open scoped NNReal

namespace ProbabilityTheory

theorem IsCagladPath.integrableOn_stieltjes {H : ℝ≥0 → ℝ} (hr : IsCagladPath H)
    (A : StieltjesFunction ℝ≥0) (T : ℝ≥0) : IntegrableOn H (Ioc 0 T) A.measure := by
  let hv : LocallyBoundedVariationOn A univ :=
    (A.mono.monotoneOn univ).locallyBoundedVariationOn
  have h := integrableOn_variationStieltjes_of_adapted_caglad
    (F := (⊥ : Filtration ℝ≥0 (inferInstance : MeasurableSpace Unit)))
    (fun t (_ : Unit) ↦ A t) (fun _ ↦ hv) (fun _ ↦ A.right_continuous)
    (H := fun t (_ : Unit) ↦ H t) (fun _ ↦ measurable_const) (fun _ ↦ hr) T ()
  simpa only [totalVariationStieltjes_measure_of_stieltjes] using h

theorem IsCagladPath.summable_abs_stieltjes_weighted_jumps {H : ℝ≥0 → ℝ}
    (hr : IsCagladPath H) (A : StieltjesFunction ℝ≥0) (T : ℝ≥0) :
    Summable (fun t : Ioc 0 T ↦ |H t * (A t - Function.leftLim A t)|) := by
  obtain ⟨C, _, hC⟩ := hr.exists_norm_bound_Icc T
  exact summable_abs_stieltjes_weighted_jumps_of_bounded A T
    (fun t ht ↦ by simpa only [Real.norm_eq_abs] using hC t ⟨ht.1.le, ht.2⟩)

end ProbabilityTheory
