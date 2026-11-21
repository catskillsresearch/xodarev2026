/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.Semimartingale.QuadraticVariation.ContinuousPartAlgebra
public import StochLean.Probability.Process.Path.LeftLimitAddition
public import StochLean.ForMathlib.Analysis.SummableSquarePolarization

/-! # The continuous component of mixed quadratic covariation

Polarization is applied to the continuous components of the same raw square
brackets. The actual mixed-jump series is absolutely summable, and the raw
covariation decomposes into its initial product, continuous part and that series.
Mixed continuous covariation is not asserted to be increasing.
-/

@[expose] public section

open MeasureTheory StochLean Set Filter
open scoped NNReal

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsFiniteMeasure P]
  {F : Filtration ℝ≥0 mΩ} {X Y : ℝ≥0 → Ω → ℝ}

noncomputable def IsSemimartingale.continuousQuadraticCovariation
    (hX : IsSemimartingale X F P) (hY : IsSemimartingale Y F P) (hF : F.IsUsual P) :
    ℝ≥0 → Ω → ℝ := fun t ω ↦ (1 / 2 : ℝ) *
      ((hX.add hY).continuousQuadraticVariation hF t ω - hX.continuousQuadraticVariation hF t ω -
        hY.continuousQuadraticVariation hF t ω)

theorem IsSemimartingale.continuousQuadraticCovariation_proof_irrel
    (hX hX' : IsSemimartingale X F P) (hY hY' : IsSemimartingale Y F P)
    (hF hF' : F.IsUsual P) :
    hX.continuousQuadraticCovariation hY hF = hX'.continuousQuadraticCovariation hY' hF' := rfl

theorem IsSemimartingale.adapted_continuousQuadraticCovariation
    (hX : IsSemimartingale X F P) (hY : IsSemimartingale Y F P) (hF : F.IsUsual P) :
    Adapted F (hX.continuousQuadraticCovariation hY hF) := fun t ↦
  ((((hX.add hY).adapted_continuousQuadraticVariation hF t).sub
    (hX.adapted_continuousQuadraticVariation hF t)).sub
    (hY.adapted_continuousQuadraticVariation hF t)).const_mul (1 / 2)

theorem IsSemimartingale.continuousQuadraticCovariation_zero
    (hX : IsSemimartingale X F P) (hY : IsSemimartingale Y F P) (hF : F.IsUsual P) (ω : Ω) :
    hX.continuousQuadraticCovariation hY hF 0 ω = 0 := by
  simp only [continuousQuadraticCovariation, continuousQuadraticVariation_zero,
    sub_self, mul_zero]

theorem IsSemimartingale.continuous_continuousQuadraticCovariation
    (hX : IsSemimartingale X F P) (hY : IsSemimartingale Y F P) (hF : F.IsUsual P) (ω : Ω) :
    Continuous (fun t ↦ hX.continuousQuadraticCovariation hY hF t ω) :=
  ((((hX.add hY).continuous_continuousQuadraticVariation hF ω).sub
    (hX.continuous_continuousQuadraticVariation hF ω)).sub
    (hY.continuous_continuousQuadraticVariation hF ω)).const_mul (1 / 2)

theorem IsSemimartingale.hasContinuousPaths_continuousQuadraticCovariation
    (hX : IsSemimartingale X F P) (hY : IsSemimartingale Y F P) (hF : F.IsUsual P) :
    HasContinuousPaths (hX.continuousQuadraticCovariation hY hF) P :=
  Eventually.of_forall (hX.continuous_continuousQuadraticCovariation hY hF)

theorem IsSemimartingale.hasFiniteVariationPaths_continuousQuadraticCovariation
    (hX : IsSemimartingale X F P) (hY : IsSemimartingale Y F P) (hF : F.IsUsual P) :
    HasFiniteVariationPaths (hX.continuousQuadraticCovariation hY hF) P := by
  apply Eventually.of_forall
  intro ω
  have hhalf {f : ℝ≥0 → ℝ} (hf : Monotone f) : Monotone (fun t ↦ (1 / 2 : ℝ) * f t) :=
    fun _ _ hst ↦ mul_le_mul_of_nonneg_left (hf hst) (by norm_num)
  have hsum := hhalf ((hX.add hY).monotone_continuousQuadraticVariation hF ω)
  have hx := hhalf (hX.monotone_continuousQuadraticVariation hF ω)
  have hy := hhalf (hY.monotone_continuousQuadraticVariation hF ω)
  have hv := locallyBoundedVariationOn_sub
    (locallyBoundedVariationOn_sub (hsum.monotoneOn univ).locallyBoundedVariationOn
      (hx.monotoneOn univ).locallyBoundedVariationOn) (hy.monotoneOn univ).locallyBoundedVariationOn
  convert! hv using 1
  funext t
  dsimp only [continuousQuadraticCovariation]
  ring

theorem IsSemimartingale.isSemimartingale_continuousQuadraticCovariation
    (hX : IsSemimartingale X F P) (hY : IsSemimartingale Y F P) (hF : F.IsUsual P) :
    IsSemimartingale (hX.continuousQuadraticCovariation hY hF) F P :=
  (hX.hasFiniteVariationPaths_continuousQuadraticCovariation hY hF).isSemimartingale
    (hX.adapted_continuousQuadraticCovariation hY hF) hF
    (hX.hasContinuousPaths_continuousQuadraticCovariation hY hF).hasCadlagPaths

theorem IsSemimartingale.quadraticCovariation_continuous_jump_decomposition
    (hX : IsSemimartingale X F P) (hY : IsSemimartingale Y F P) (hF : F.IsUsual P) :
    ∀ᵐ ω ∂P, ∀ t : ℝ≥0,
      Summable (fun s : Ioc 0 t ↦ |jumpProcess X s ω * jumpProcess Y s ω|) ∧
      hX.quadraticCovariation hY hF t ω = X 0 ω * Y 0 ω +
        hX.continuousQuadraticCovariation hY hF t ω +
          ∑' s : Ioc 0 t, jumpProcess X s ω * jumpProcess Y s ω := by
  filter_upwards [hX.quadraticVariation_continuous_jump_decomposition hF,
    hY.quadraticVariation_continuous_jump_decomposition hF,
    (hX.add hY).quadraticVariation_continuous_jump_decomposition hF,
    hX.hasCadlagPaths, hY.hasCadlagPaths] with ω hx hy hz hcx hcy t
  have hsum : (∑' s : Ioc 0 t, (jumpProcess (X + Y) s ω) ^ 2) =
      (∑' s : Ioc 0 t, (jumpProcess X s ω) ^ 2) +
        2 * (∑' s : Ioc 0 t, jumpProcess X s ω * jumpProcess Y s ω) +
          (∑' s : Ioc 0 t, (jumpProcess Y s ω) ^ 2) := by
    calc
      _ = ∑' s : Ioc 0 t, (jumpProcess X s ω + jumpProcess Y s ω) ^ 2 := by
        apply tsum_congr
        intro s
        rw [hcx.jumpProcess_add hcy s]
      _ = _ := tsum_sq_add_of_summable_sq (hx t).1 (hy t).1
  refine ⟨summable_abs_mul_of_summable_sq (hx t).1 (hy t).1, ?_⟩
  rw [quadraticCovariation, (hz t).2, (hx t).2, (hy t).2, hsum]
  simp only [continuousQuadraticCovariation, Pi.add_apply]
  ring

end ProbabilityTheory
