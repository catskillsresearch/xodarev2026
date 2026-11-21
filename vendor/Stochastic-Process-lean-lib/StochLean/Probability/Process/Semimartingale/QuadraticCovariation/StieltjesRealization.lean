/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.Semimartingale.QuadraticCovariation.KunitaWatanabeInitial
public import StochLean.Probability.Process.FiniteVariation.StieltjesRealization
public import StochLean.ForMathlib.MeasureTheory.MeasurableStieltjesLIntegral

/-! # Measurable Stieltjes realizations of the canonical raw brackets

These are null-event versions of the already constructed brackets, not another
definition of stochastic quadratic variation. All three path identifications
are indistinguishability statements. Their canonical variation/energy integrals
will therefore have measurable random versions without assumptions on moments.
-/

@[expose] public section

open MeasureTheory StochLean Set
open scoped NNReal ENNReal

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsFiniteMeasure P]
  {F : Filtration ℝ≥0 mΩ} {X Y : ℝ≥0 → Ω → ℝ}

structure SemimartingaleBracketRealization
    (hX : IsSemimartingale X F P) (hY : IsSemimartingale Y F P) (hF : F.IsUsual P) where
  mixed : ℝ≥0 → Ω → ℝ
  mixed_adapted : Adapted F mixed
  mixed_bv : ∀ ω, LocallyBoundedVariationOn (fun t ↦ mixed t ω) univ
  mixed_rc : ∀ ω, IsRightContinuousPath (fun t ↦ mixed t ω)
  mixed_eq : Indistinguishable (hX.quadraticCovariation hY hF) mixed P
  left : Ω → StieltjesFunction ℝ≥0
  right : Ω → StieltjesFunction ℝ≥0
  left_adapted : Adapted F (fun t ω ↦ left ω t)
  right_adapted : Adapted F (fun t ω ↦ right ω t)
  left_eq : Indistinguishable (hX.quadraticVariation hF) (fun t ω ↦ left ω t) P
  right_eq : Indistinguishable (hY.quadraticVariation hF) (fun t ω ↦ right ω t) P

theorem IsSemimartingale.nonempty_bracketRealization
    (hX : IsSemimartingale X F P) (hY : IsSemimartingale Y F P) (hF : F.IsUsual P) :
    Nonempty (SemimartingaleBracketRealization hX hY hF) := by
  obtain ⟨A, heq, ha, hA⟩ :=
    (hX.adapted_quadraticCovariation hY hF).exists_cadlag_finiteVariation_indistinguishable_of_usual
      hF (hX.hasCadlagPaths_quadraticCovariation hY hF)
      (hX.hasFiniteVariationPaths_quadraticCovariation hY hF)
  obtain ⟨B, hb, hB⟩ :=
    (hX.adapted_quadraticVariation hF).exists_stieltjes_indistinguishable_of_usual hF
      (hX.hasMonotonePaths_quadraticVariation hF)
      (hX.hasCadlagPaths_quadraticVariation hF).hasRightContinuousPaths
  obtain ⟨C, hc, hC⟩ :=
    (hY.adapted_quadraticVariation hF).exists_stieltjes_indistinguishable_of_usual hF
      (hY.hasMonotonePaths_quadraticVariation hF)
      (hY.hasCadlagPaths_quadraticVariation hF).hasRightContinuousPaths
  exact ⟨⟨A, ha.stronglyAdapted.adapted, fun ω ↦ (hA ω).2, fun ω ↦ (hA ω).1.1,
    heq, B, C, hb, hc, hB, hC⟩⟩

namespace SemimartingaleBracketRealization

variable {hX : IsSemimartingale X F P} {hY : IsSemimartingale Y F P} {hF : F.IsUsual P}
  (D : SemimartingaleBracketRealization hX hY hF)

noncomputable def variation (ω : Ω) : StieltjesFunction ℝ≥0 :=
  totalVariationStieltjes (fun t ↦ D.mixed t ω) (D.mixed_bv ω) (D.mixed_rc ω)

theorem adapted_variation : Adapted F (fun t ω ↦ D.variation ω t) :=
  D.mixed_adapted.totalVariationProcess_of_rightContinuous D.mixed_rc

theorem measurable_variation_lintegral {f : Ω × ℝ≥0 → ℝ≥0∞} (hf : Measurable f) :
    Measurable fun ω ↦ ∫⁻ t, f (ω, t) ∂(D.variation ω).measure :=
  measurable_stieltjesLIntegral (fun t ↦ (D.adapted_variation t).mono (F.le t) le_rfl) hf

theorem measurable_left_lintegral {f : Ω × ℝ≥0 → ℝ≥0∞} (hf : Measurable f) :
    Measurable fun ω ↦ ∫⁻ t, f (ω, t) ∂(D.left ω).measure :=
  measurable_stieltjesLIntegral (fun t ↦ (D.left_adapted t).mono (F.le t) le_rfl) hf

theorem measurable_right_lintegral {f : Ω × ℝ≥0 → ℝ≥0∞} (hf : Measurable f) :
    Measurable fun ω ↦ ∫⁻ t, f (ω, t) ∂(D.right ω).measure :=
  measurable_stieltjesLIntegral (fun t ↦ (D.right_adapted t).mono (F.le t) le_rfl) hf

theorem increment_bound : ∀ᵐ ω ∂P, ∀ s t, s ≤ t →
    |D.mixed t ω - D.mixed s ω| ≤
      Real.sqrt (D.left ω t - D.left ω s) * Real.sqrt (D.right ω t - D.right ω s) := by
  filter_upwards [D.mixed_eq, D.left_eq, D.right_eq,
    hX.abs_quadraticCovariation_increment_le hY hF] with ω hA hB hC hinc s t hst
  simpa only [← hA, ← hB, ← hC] using hinc s t hst

end SemimartingaleBracketRealization

end ProbabilityTheory
