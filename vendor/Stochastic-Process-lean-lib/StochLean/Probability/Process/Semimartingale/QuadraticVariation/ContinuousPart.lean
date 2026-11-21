/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.Semimartingale.QuadraticCovariation.StieltjesRealization
public import StochLean.Probability.Process.FiniteVariation.ContinuousPart
public import StochLean.Analysis.PathVariation.StieltjesJumpSum

/-! # The continuous component of the unique raw quadratic variation

The definition removes the point atoms of a genuine Stieltjes version of the
already constructed raw bracket. It is not a second quadratic-variation
construction. Its exact decomposition uses the squared jumps of the original
semimartingale, with the initial square separate and summability proved.
-/

@[expose] public section

open MeasureTheory StochLean Set Filter
open scoped NNReal

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsFiniteMeasure P]
  {F : Filtration ℝ≥0 mΩ} {X : ℝ≥0 → Ω → ℝ}

noncomputable def IsSemimartingale.continuousQuadraticVariation
    (hX : IsSemimartingale X F P) (hF : F.IsUsual P) : ℝ≥0 → Ω → ℝ :=
  fun t ω ↦ stieltjesContinuousPart
    ((Classical.choice (hX.nonempty_bracketRealization hX hF)).left ω) t

theorem IsSemimartingale.continuousQuadraticVariation_proof_irrel
    (hX hX' : IsSemimartingale X F P) (hF hF' : F.IsUsual P) :
    hX.continuousQuadraticVariation hF = hX'.continuousQuadraticVariation hF' := rfl

theorem IsSemimartingale.adapted_continuousQuadraticVariation
    (hX : IsSemimartingale X F P) (hF : F.IsUsual P) :
    Adapted F (hX.continuousQuadraticVariation hF) :=
  adapted_stieltjesContinuousPart
    (Classical.choice (hX.nonempty_bracketRealization hX hF)).left_adapted

theorem IsSemimartingale.continuousQuadraticVariation_zero
    (hX : IsSemimartingale X F P) (hF : F.IsUsual P) (ω : Ω) :
    hX.continuousQuadraticVariation hF 0 ω = 0 := stieltjesContinuousPart_zero _

theorem IsSemimartingale.continuous_continuousQuadraticVariation
    (hX : IsSemimartingale X F P) (hF : F.IsUsual P) (ω : Ω) :
    Continuous (fun t ↦ hX.continuousQuadraticVariation hF t ω) :=
  continuous_stieltjesContinuousPart _

theorem IsSemimartingale.monotone_continuousQuadraticVariation
    (hX : IsSemimartingale X F P) (hF : F.IsUsual P) (ω : Ω) :
    Monotone (fun t ↦ hX.continuousQuadraticVariation hF t ω) :=
  (stieltjesContinuousPart _).mono

theorem IsSemimartingale.hasContinuousPaths_continuousQuadraticVariation
    (hX : IsSemimartingale X F P) (hF : F.IsUsual P) :
    HasContinuousPaths (hX.continuousQuadraticVariation hF) P :=
  Eventually.of_forall (hX.continuous_continuousQuadraticVariation hF)

theorem IsSemimartingale.hasFiniteVariationPaths_continuousQuadraticVariation
    (hX : IsSemimartingale X F P) (hF : F.IsUsual P) :
    HasFiniteVariationPaths (hX.continuousQuadraticVariation hF) P :=
  (show HasMonotonePaths (hX.continuousQuadraticVariation hF) P from
    Eventually.of_forall (hX.monotone_continuousQuadraticVariation hF)).hasFiniteVariationPaths

theorem IsSemimartingale.isSemimartingale_continuousQuadraticVariation
    (hX : IsSemimartingale X F P) (hF : F.IsUsual P) :
    IsSemimartingale (hX.continuousQuadraticVariation hF) F P :=
  (hX.hasFiniteVariationPaths_continuousQuadraticVariation hF).isSemimartingale
    (hX.adapted_continuousQuadraticVariation hF) hF
    (hX.hasContinuousPaths_continuousQuadraticVariation hF).hasCadlagPaths

theorem IsSemimartingale.quadraticVariation_continuous_jump_decomposition
    (hX : IsSemimartingale X F P) (hF : F.IsUsual P) :
    ∀ᵐ ω ∂P, ∀ t : ℝ≥0,
      Summable (fun s : Ioc 0 t ↦ (jumpProcess X s ω) ^ 2) ∧
      hX.quadraticVariation hF t ω = (X 0 ω) ^ 2 + hX.continuousQuadraticVariation hF t ω +
        ∑' s : Ioc 0 t, (jumpProcess X s ω) ^ 2 := by
  let D := Classical.choice (hX.nonempty_bracketRealization hX hF)
  filter_upwards [D.left_eq, hX.quadraticVariation_zero_ae hF,
    hX.jumpProcess_quadraticVariation hF] with ω heq h0 hj t
  have hjump (s : Ioc 0 t) : D.left ω s - Function.leftLim (D.left ω) s =
      (jumpProcess X s ω) ^ 2 := by
    have hs : (s : ℝ≥0) ≠ 0 := ne_of_gt s.2.1
    have h := hj s
    change hX.quadraticVariation hF s ω - leftLimitProcess (hX.quadraticVariation hF) s ω = _ at h
    simp only [leftLimitProcess, if_neg hs, heq] at h
    exact h
  have hsum := summable_stieltjes_jumps (D.left ω) t
  have hdecomp := stieltjes_continuous_jump_decomposition (D.left ω) t
  have hinit : D.left ω 0 = (X 0 ω) ^ 2 := (heq 0).symm.trans h0
  refine ⟨?_, ?_⟩
  · simpa only [hjump] using hsum
  · simpa only [hjump, hinit, heq, continuousQuadraticVariation] using hdecomp

theorem IsSemimartingale.summable_sq_jumps
    (hX : IsSemimartingale X F P) (hF : F.IsUsual P) :
    ∀ᵐ ω ∂P, ∀ t : ℝ≥0, Summable (fun s : Ioc 0 t ↦ (jumpProcess X s ω) ^ 2) :=
  (hX.quadraticVariation_continuous_jump_decomposition hF).mono fun _ h t ↦ (h t).1

end ProbabilityTheory
