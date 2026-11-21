/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.Semimartingale.QuadraticCovariation.IntegralAlgebra
public import StochLean.Probability.Process.UCP.CadlagMultiplication
public import StochLean.Probability.Process.UCP.LeftLimit

/-! # Brackets are UCP-continuous along integrals of one fixed integrator

This is the extension step in Protter II.29. It uses the product formula,
associativity and continuity in the integrand. It does not assert continuity
of brackets or stochastic integrals for arbitrary varying semimartingales.
-/

@[expose] public section

open MeasureTheory Filter
open scoped NNReal

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsFiniteMeasure P]
  {F : Filtration ℝ≥0 mΩ} {X Y H : ℝ≥0 → Ω → ℝ} {K : ℕ → ℝ≥0 → Ω → ℝ}

theorem IsSemimartingale.quadraticCovariation_stochasticIntegral_eq_product
    (hX : IsSemimartingale X F P) (hY : IsSemimartingale Y F P) (hF : F.IsUsual P)
    (ha : Adapted F H) (hr : HasCagladPaths H P) :
    let hJ := hX.isSemimartingale_stochasticIntegral hF ha hr
    Indistinguishable (hJ.quadraticCovariation hY hF)
      (hX.stochasticIntegral hF ha hr * Y -
        hY.stochasticIntegral hF
          (hJ.adapted.leftLimitProcess_of_usual hF hJ.hasCadlagPaths)
          hJ.hasCadlagPaths.hasCagladPaths_leftLimitProcess -
        hX.stochasticIntegral hF
          (fun t ↦ (hY.adapted.leftLimitProcess_of_usual hF hY.hasCadlagPaths t).mul (ha t))
          (hY.hasCadlagPaths.hasCagladPaths_leftLimitProcess.mul hr)) P := by
  dsimp only
  let hJ := hX.isSemimartingale_stochasticIntegral hF ha hr
  have hassoc := hX.stochasticIntegral_stochasticIntegral hF
    (hY.adapted.leftLimitProcess_of_usual hF hY.hasCadlagPaths)
    hY.hasCadlagPaths.hasCagladPaths_leftLimitProcess ha hr
  filter_upwards [hJ.quadraticCovariation_eq_product_sub_integrals hY hF, hassoc]
    with ω he ha t
  simp only [he t, Pi.sub_apply, ha t]

theorem IsSemimartingale.tendstoUCP_quadraticCovariation_stochasticIntegral
    (hX : IsSemimartingale X F P) (hY : IsSemimartingale Y F P) (hF : F.IsUsual P)
    (haH : Adapted F H) (hrH : HasCagladPaths H P)
    (haK : ∀ n, Adapted F (K n)) (hrK : ∀ n, HasCagladPaths (K n) P)
    (hu : TendstoUCP P K atTop H) :
    TendstoUCP P
      (fun n ↦ IsSemimartingale.quadraticCovariation
        (hX.isSemimartingale_stochasticIntegral hF (haK n) (hrK n)) hY hF) atTop
      ((hX.isSemimartingale_stochasticIntegral hF haH hrH).quadraticCovariation hY hF) := by
  let J := hX.stochasticIntegral hF haH hrH
  let Jn := fun n ↦ hX.stochasticIntegral hF (haK n) (hrK n)
  let hJ := hX.isSemimartingale_stochasticIntegral hF haH hrH
  let hJn := fun n ↦ hX.isSemimartingale_stochasticIntegral hF (haK n) (hrK n)
  let haYL := hY.adapted.leftLimitProcess_of_usual hF hY.hasCadlagPaths
  let hrYL := hY.hasCadlagPaths.hasCagladPaths_leftLimitProcess
  have huJ : TendstoUCP P Jn atTop J :=
    hX.tendstoUCP_stochasticIntegral hF haH hrH haK hrK hu
  have huProd := huJ.mul_right_of_cadlag
    (fun n t ↦ ((hJn n).adapted t).mono (F.le t) le_rfl)
    (fun t ↦ (hJ.adapted t).mono (F.le t) le_rfl)
    (fun t ↦ (hY.adapted t).mono (F.le t) le_rfl)
    (fun n ↦ (hJn n).hasCadlagPaths) hJ.hasCadlagPaths hY.hasCadlagPaths
  have huJL := huJ.leftLimitProcess_of_cadlag (fun n ↦ (hJn n).hasCadlagPaths)
    hJ.hasCadlagPaths
  have huY := hY.tendstoUCP_stochasticIntegral hF
    (hJ.adapted.leftLimitProcess_of_usual hF hJ.hasCadlagPaths)
    hJ.hasCadlagPaths.hasCagladPaths_leftLimitProcess
    (fun n ↦ (hJn n).adapted.leftLimitProcess_of_usual hF (hJn n).hasCadlagPaths)
    (fun n ↦ (hJn n).hasCadlagPaths.hasCagladPaths_leftLimitProcess) huJL
  have huK := hu.mul_left_of_caglad
    (fun n t ↦ (haK n t).mono (F.le t) le_rfl)
    (fun t ↦ (haH t).mono (F.le t) le_rfl)
    (fun t ↦ (haYL t).mono (F.le t) le_rfl) hrK hrH hrYL
  have huX := hX.tendstoUCP_stochasticIntegral hF
    (fun t ↦ (haYL t).mul (haH t)) (hrYL.mul hrH)
    (fun n t ↦ (haYL t).mul (haK n t)) (fun n ↦ hrYL.mul (hrK n)) huK
  exact (((huProd.sub huY).sub huX).congr_left
    (fun n ↦ (hX.quadraticCovariation_stochasticIntegral_eq_product hY hF
      (haK n) (hrK n)).symm)).congr_right
        (hX.quadraticCovariation_stochasticIntegral_eq_product hY hF haH hrH).symm

end ProbabilityTheory
