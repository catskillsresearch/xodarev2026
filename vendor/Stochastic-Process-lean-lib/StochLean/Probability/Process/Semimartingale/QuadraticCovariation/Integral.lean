/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.Semimartingale.QuadraticCovariation.SimpleIntegral

/-! # Protter II.29: covariation of stochastic integrals

Simple predictable integrands are handled by their actual finite mixed sums.
UCP approximation then proves the identity for all adapted caglad integrands.
Symmetry and associativity give the two-integral form. All initial terms are
retained and the existing raw bracket and general integral remain the owners.
-/

@[expose] public section

open MeasureTheory Filter
open scoped NNReal

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsFiniteMeasure P]
  {F : Filtration ℝ≥0 mΩ} {X Y H K : ℝ≥0 → Ω → ℝ}

theorem IsSemimartingale.quadraticCovariation_stochasticIntegral_left
    (hX : IsSemimartingale X F P) (hY : IsSemimartingale Y F P) (hF : F.IsUsual P)
    (ha : Adapted F H) (hr : HasCagladPaths H P) :
    Indistinguishable
      ((hX.isSemimartingale_stochasticIntegral hF ha hr).quadraticCovariation hY hF)
      ((hX.isSemimartingale_quadraticCovariation hY hF).stochasticIntegral hF ha hr) P := by
  obtain ⟨S, hS, huS⟩ := exists_simplePredictable_tendstoUCP ha hF hr
  let hB := hX.isSemimartingale_quadraticCovariation hY hF
  let hJ := hX.isSemimartingale_stochasticIntegral hF ha hr
  have huL := hX.tendstoUCP_quadraticCovariation_stochasticIntegral hY hF ha hr
    (fun n ↦ (hS n).adapted) (fun n ↦ (hS n).hasCagladPaths P) huS
  have huR := hB.tendstoUCP_stochasticIntegral hF ha hr
    (fun n ↦ (hS n).adapted) (fun n ↦ (hS n).hasCagladPaths P) huS
  exact (huL.congr_left (fun n ↦ hX.quadraticCovariation_stochasticIntegral_of_simple hY hF
    (hS n).adapted ((hS n).hasCagladPaths P) (hS n))).indistinguishable_unique huR
      (hJ.hasCadlagPaths_quadraticCovariation hY hF).hasRightContinuousPaths
      (hB.hasCadlagPaths_stochasticIntegral hF ha hr).hasRightContinuousPaths

theorem IsSemimartingale.quadraticCovariation_stochasticIntegral_right
    (hX : IsSemimartingale X F P) (hY : IsSemimartingale Y F P) (hF : F.IsUsual P)
    (ha : Adapted F H) (hr : HasCagladPaths H P) :
    Indistinguishable
      (hX.quadraticCovariation (hY.isSemimartingale_stochasticIntegral hF ha hr) hF)
      ((hX.isSemimartingale_quadraticCovariation hY hF).stochasticIntegral hF ha hr) P := by
  have hi := IsSemimartingale.stochasticIntegral_congr_integrator
    (hY.isSemimartingale_quadraticCovariation hX hF)
    (hX.isSemimartingale_quadraticCovariation hY hF) hF ha hr
    (hY.quadraticCovariation_comm hX hF)
  exact (hX.quadraticCovariation_comm
    (hY.isSemimartingale_stochasticIntegral hF ha hr) hF).trans
      ((hY.quadraticCovariation_stochasticIntegral_left hX hF ha hr).trans hi)

theorem IsSemimartingale.quadraticCovariation_stochasticIntegral_both
    (hX : IsSemimartingale X F P) (hY : IsSemimartingale Y F P) (hF : F.IsUsual P)
    (haH : Adapted F H) (hrH : HasCagladPaths H P)
    (haK : Adapted F K) (hrK : HasCagladPaths K P) :
    Indistinguishable
      ((hX.isSemimartingale_stochasticIntegral hF haH hrH).quadraticCovariation
        (hY.isSemimartingale_stochasticIntegral hF haK hrK) hF)
      ((hX.isSemimartingale_quadraticCovariation hY hF).stochasticIntegral hF
        (fun t ↦ (haH t).mul (haK t)) (hrH.mul hrK)) P := by
  let hJY := hY.isSemimartingale_stochasticIntegral hF haK hrK
  let hB := hX.isSemimartingale_quadraticCovariation hY hF
  have hi := IsSemimartingale.stochasticIntegral_congr_integrator
    (hX.isSemimartingale_quadraticCovariation hJY hF)
    (hB.isSemimartingale_stochasticIntegral hF haK hrK) hF haH hrH
    (hX.quadraticCovariation_stochasticIntegral_right hY hF haK hrK)
  exact (hX.quadraticCovariation_stochasticIntegral_left hJY hF haH hrH).trans
    (hi.trans (hB.stochasticIntegral_stochasticIntegral hF haH hrH haK hrK))

end ProbabilityTheory
