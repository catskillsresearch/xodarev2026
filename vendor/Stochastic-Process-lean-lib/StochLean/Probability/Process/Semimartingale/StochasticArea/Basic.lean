/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.Semimartingale.StochasticIntegral.ContinuousPaths
public import StochLean.Probability.Process.Semimartingale.StochasticIntegral.InitialValue
public import
  StochLean.Probability.Process.Semimartingale.StochasticIntegral.SemimartingalePreservation
public import StochLean.Probability.Process.Semimartingale.Subtraction

/-! # The actual antisymmetric stochastic area integral

The source area is `integral X_- dY - integral Y_- dX`, using the sole
Chapter II stochastic integral. It is twice the signed geometric area in
Protter's convention. It starts at zero even for arbitrary initial values.
Continuous local-martingale coordinates give a continuous local martingale;
neither Brownian laws nor a bracket formula are built into the definition.
-/

@[expose] public section

open MeasureTheory Filter
open scoped NNReal

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsFiniteMeasure P]
  {F : Filtration ℝ≥0 mΩ} {X Y : ℝ≥0 → Ω → ℝ}

noncomputable def IsSemimartingale.stochasticArea
    (hX : IsSemimartingale X F P) (hY : IsSemimartingale Y F P) (hF : F.IsUsual P) :
    ℝ≥0 → Ω → ℝ :=
  hY.stochasticIntegral hF (hX.adapted.leftLimitProcess_of_usual hF hX.hasCadlagPaths)
    hX.hasCadlagPaths.hasCagladPaths_leftLimitProcess -
  hX.stochasticIntegral hF (hY.adapted.leftLimitProcess_of_usual hF hY.hasCadlagPaths)
    hY.hasCadlagPaths.hasCagladPaths_leftLimitProcess

theorem IsSemimartingale.stochasticArea_antisymm
    (hX : IsSemimartingale X F P) (hY : IsSemimartingale Y F P) (hF : F.IsUsual P) :
    hX.stochasticArea hY hF = -hY.stochasticArea hX hF := by
  exact (neg_sub _ _).symm

theorem IsSemimartingale.stochasticArea_self
    (hX : IsSemimartingale X F P) (hF : F.IsUsual P) : hX.stochasticArea hX hF = 0 :=
  sub_self _

theorem IsSemimartingale.stochasticArea_zero_ae
    (hX : IsSemimartingale X F P) (hY : IsSemimartingale Y F P) (hF : F.IsUsual P) :
    hX.stochasticArea hY hF 0 =ᵐ[P] 0 := by
  filter_upwards [hY.stochasticIntegral_zero_ae hF
    (hX.adapted.leftLimitProcess_of_usual hF hX.hasCadlagPaths)
      hX.hasCadlagPaths.hasCagladPaths_leftLimitProcess,
    hX.stochasticIntegral_zero_ae hF
      (hY.adapted.leftLimitProcess_of_usual hF hY.hasCadlagPaths)
        hY.hasCadlagPaths.hasCagladPaths_leftLimitProcess] with ω hxy hyx
  change _ - _ = (0 : ℝ)
  rw [hxy, hyx]
  simp only [leftLimitProcess_zero, Pi.zero_apply, zero_mul, sub_self]

theorem IsSemimartingale.isSemimartingale_stochasticArea
    (hX : IsSemimartingale X F P) (hY : IsSemimartingale Y F P) (hF : F.IsUsual P) :
    IsSemimartingale (hX.stochasticArea hY hF) F P :=
  (hY.isSemimartingale_stochasticIntegral hF
    (hX.adapted.leftLimitProcess_of_usual hF hX.hasCadlagPaths)
      hX.hasCadlagPaths.hasCagladPaths_leftLimitProcess).sub
    (hX.isSemimartingale_stochasticIntegral hF
      (hY.adapted.leftLimitProcess_of_usual hF hY.hasCadlagPaths)
        hY.hasCadlagPaths.hasCagladPaths_leftLimitProcess)

theorem IsSemimartingale.hasContinuousPaths_stochasticArea
    (hX : IsSemimartingale X F P) (hY : IsSemimartingale Y F P) (hF : F.IsUsual P)
    (hcX : HasContinuousPaths X P) (hcY : HasContinuousPaths Y P) :
    HasContinuousPaths (hX.stochasticArea hY hF) P := by
  filter_upwards [hY.hasContinuousPaths_stochasticIntegral hF
    (hX.adapted.leftLimitProcess_of_usual hF hX.hasCadlagPaths)
      hX.hasCadlagPaths.hasCagladPaths_leftLimitProcess hcY,
    hX.hasContinuousPaths_stochasticIntegral hF
      (hY.adapted.leftLimitProcess_of_usual hF hY.hasCadlagPaths)
        hY.hasCadlagPaths.hasCagladPaths_leftLimitProcess hcX] with ω hxy hyx
  exact hxy.sub hyx

theorem IsContinuousLocalMartingale.isContinuousLocalMartingale_stochasticArea
    (hX : IsContinuousLocalMartingale X F P) (hY : IsContinuousLocalMartingale Y F P)
    (hF : F.IsUsual P) :
    IsContinuousLocalMartingale
      ((hX.isSemimartingale hF).stochasticArea (hY.isSemimartingale hF) hF) F P := by
  let hSX := hX.isSemimartingale hF
  let hSY := hY.isSemimartingale hF
  have hxy := hY.isContinuousLocalMartingale_stochasticIntegral hF
    (hSX.adapted.leftLimitProcess_of_usual hF hSX.hasCadlagPaths)
      hSX.hasCadlagPaths.hasCagladPaths_leftLimitProcess
  have hyx := hX.isContinuousLocalMartingale_stochasticIntegral hF
    (hSY.adapted.leftLimitProcess_of_usual hF hSY.hasCadlagPaths)
      hSY.hasCadlagPaths.hasCagladPaths_leftLimitProcess
  exact ⟨hxy.1.sub hyx.1 hF, hSX.hasContinuousPaths_stochasticArea hSY hF hX.2 hY.2⟩

end ProbabilityTheory
