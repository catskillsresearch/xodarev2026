/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.Semimartingale.QuadraticCovariation.Riemann
public import StochLean.Probability.Process.Partition.CrossSumsProduct
public import StochLean.Probability.Process.Path.Multiplication
public import StochLean.Probability.Process.Semimartingale.StochasticIntegral.SemimartingalePreservation
public import StochLean.Probability.Process.Semimartingale.Localization

/-! # Integration by parts and the algebra of semimartingales

The identity is deduced from actual random-partition mixed sums and the
cadlag-integrand Riemann theorem. It identifies the existing polarized bracket;
the product formula is not used as a competing definition of covariation.
-/

@[expose] public section

open MeasureTheory
open scoped NNReal

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsFiniteMeasure P]
  {F : Filtration ℝ≥0 mΩ} {X Y : ℝ≥0 → Ω → ℝ}

theorem IsSemimartingale.quadraticCovariation_eq_product_sub_integrals
    (hX : IsSemimartingale X F P) (hY : IsSemimartingale Y F P) (hF : F.IsUsual P) :
    Indistinguishable (hX.quadraticCovariation hY hF)
      (X * Y - hY.stochasticIntegral hF
        (hX.adapted.leftLimitProcess_of_usual hF hX.hasCadlagPaths)
        hX.hasCadlagPaths.hasCagladPaths_leftLimitProcess -
      hX.stochasticIntegral hF
        (hY.adapted.leftLimitProcess_of_usual hF hY.hasCadlagPaths)
        hY.hasCadlagPaths.hasCagladPaths_leftLimitProcess) P := by
  apply hX.quadraticCovariation_indistinguishable_of_limits hY hF
  · intro π hπ
    have hprod := hπ.tendstoUCP_min_terminal (X * Y)
    have hu := (hprod.sub (hY.tendstoUCP_leftRiemannSum_leftLimit_of_cadlag
      hF hX.adapted hX.hasCadlagPaths hπ)).sub
        (hX.tendstoUCP_leftRiemannSum_leftLimit_of_cadlag hF hY.adapted hY.hasCadlagPaths hπ)
    have heq (n : ℕ) :
        (fun t ω ↦ (X * Y) (min ((π n).terminal ω) t) ω) -
          (π n).leftRiemannSumProcess X Y - (π n).leftRiemannSumProcess Y X =
        (π n).quadraticCovariationSumProcess X Y := by
      funext t ω
      exact ((π n).quadraticCovariationSumProcess_eq_product_sub_riemann X Y t ω).symm
    rw [show (fun n ↦ (fun t ω ↦ (X * Y) (min ((π n).terminal ω) t) ω) -
      (π n).leftRiemannSumProcess X Y - (π n).leftRiemannSumProcess Y X) =
        (fun n ↦ (π n).quadraticCovariationSumProcess X Y) from funext heq] at hu
    exact hu
  · exact (((hX.hasCadlagPaths.mul hY.hasCadlagPaths).sub
      (hY.hasCadlagPaths_stochasticIntegral hF
        (hX.adapted.leftLimitProcess_of_usual hF hX.hasCadlagPaths)
        hX.hasCadlagPaths.hasCagladPaths_leftLimitProcess)).sub
      (hX.hasCadlagPaths_stochasticIntegral hF
        (hY.adapted.leftLimitProcess_of_usual hF hY.hasCadlagPaths)
        hY.hasCadlagPaths.hasCagladPaths_leftLimitProcess)).hasRightContinuousPaths

theorem IsSemimartingale.integrationByParts
    (hX : IsSemimartingale X F P) (hY : IsSemimartingale Y F P) (hF : F.IsUsual P) :
    Indistinguishable (X * Y)
      (hY.stochasticIntegral hF
        (hX.adapted.leftLimitProcess_of_usual hF hX.hasCadlagPaths)
        hX.hasCadlagPaths.hasCagladPaths_leftLimitProcess +
      hX.stochasticIntegral hF
        (hY.adapted.leftLimitProcess_of_usual hF hY.hasCadlagPaths)
        hY.hasCadlagPaths.hasCagladPaths_leftLimitProcess + hX.quadraticCovariation hY hF) P := by
  filter_upwards [hX.quadraticCovariation_eq_product_sub_integrals hY hF] with ω hω t
  simp only [Pi.add_apply, hω t, Pi.sub_apply]
  ring

theorem IsSemimartingale.mul (hX : IsSemimartingale X F P)
    (hY : IsSemimartingale Y F P) (hF : F.IsUsual P) :
    IsSemimartingale (X * Y) F P := by
  have hJY := hY.isSemimartingale_stochasticIntegral hF
    (hX.adapted.leftLimitProcess_of_usual hF hX.hasCadlagPaths)
    hX.hasCadlagPaths.hasCagladPaths_leftLimitProcess
  have hJX := hX.isSemimartingale_stochasticIntegral hF
    (hY.adapted.leftLimitProcess_of_usual hF hY.hasCadlagPaths)
    hY.hasCadlagPaths.hasCagladPaths_leftLimitProcess
  exact ((hJY.add hJX).add (hX.isSemimartingale_quadraticCovariation hY hF)).congr_of_adapted
    (hX.integrationByParts hY hF).symm (fun t ↦ (hX.adapted t).mul (hY.adapted t))

end ProbabilityTheory
