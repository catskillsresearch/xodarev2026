/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.Semimartingale.Ito.TraceZero
public import StochLean.ForMathlib.Analysis.EuclideanCoordinateLaplacian

/-! # Harmonic functions of isotropic continuous local martingales

The harmonic predicate and Laplacian are Mathlib's canonical definitions.
This theorem treats functions harmonic on the whole Euclidean space. The
general open-domain theorem is in `HarmonicOpenDomain`; the corrected classical
C2 subharmonic statement is in `SubharmonicOpenDomain`.
-/

@[expose] public section

open MeasureTheory InnerProductSpace WithLp StochLean
open scoped NNReal

namespace ProbabilityTheory

theorem isContinuousLocalMartingale_comp_harmonic_of_isotropic
    {ι Ω : Type*} [Fintype ι] {mΩ : MeasurableSpace Ω}
    {P : Measure Ω} [IsFiniteMeasure P] {F : Filtration ℝ≥0 mΩ}
    {X : ι → ℝ≥0 → Ω → ℝ} {A : ℝ≥0 → Ω → ℝ} {f : EuclideanSpace ℝ ι → ℝ}
    (hX : ∀ i, IsContinuousLocalMartingale (X i) F P) (hF : F.IsUsual P)
    (hd : ∀ i, Indistinguishable
      (((hX i).isSemimartingale hF).continuousQuadraticVariation hF) A P)
    (ho : ∀ i j, i ≠ j → Indistinguishable
      (((hX i).isSemimartingale hF).continuousQuadraticCovariation
        ((hX j).isSemimartingale hF) hF) 0 P)
    (hf : HarmonicOnNhd f Set.univ) :
    IsContinuousLocalMartingale (fun t ω ↦ f (toLp 2 (fun i ↦ X i t ω))) F P := by
  classical
  have hdf : ContDiff ℝ 2 f := contDiffOn_univ.mp hf.contDiffOn
  apply isContinuousLocalMartingale_comp_of_isotropic_trace_zero_on_paths hX hF hd ho
    (hdf.comp (PiLp.continuousLinearEquiv 2 ℝ (fun _ : ι ↦ ℝ)).symm.contDiff)
  exact Filter.Eventually.of_forall
    (fun _ _ ↦ sum_coordinateSecondDeriv_toLp_eq_zero_of_harmonic hf _)

end ProbabilityTheory
