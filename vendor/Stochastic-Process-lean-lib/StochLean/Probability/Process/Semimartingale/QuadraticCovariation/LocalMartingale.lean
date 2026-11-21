/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.Semimartingale.QuadraticCovariation.IntegrationByParts
public import StochLean.Probability.Process.Semimartingale.StochasticIntegral.LocalL2
public import StochLean.Probability.Process.LocalMartingale.Congr

/-! # Locally-L2 martingales: the product minus raw covariation is local

Protter II.27, Corollary 2, existence. The assumption is the actual masked
locally square-integrable property, not an unmasked initial-moment condition.
-/

@[expose] public section

open MeasureTheory
open scoped NNReal

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsFiniteMeasure P]
  {F : Filtration ℝ≥0 mΩ} [SigmaFiniteFiltration P F] {X Y : ℝ≥0 → Ω → ℝ}

theorem IsSemimartingale.isLocalMartingale_mul_sub_quadraticCovariation
    (hX : IsSemimartingale X F P) (hY : IsSemimartingale Y F P) (hF : F.IsUsual P)
    (hLX : Locally (fun M ↦ IsSquareIntegrableMartingale M F P) F X P)
    (hLY : Locally (fun M ↦ IsSquareIntegrableMartingale M F P) F Y P) :
    IsLocalMartingale (X * Y - hX.quadraticCovariation hY hF) F P := by
  have hJY := hY.isLocalMartingale_stochasticIntegral_of_locally_squareIntegrable hF hLY
    (hX.adapted.leftLimitProcess_of_usual hF hX.hasCadlagPaths)
    hX.hasCadlagPaths.hasCagladPaths_leftLimitProcess
  have hJX := hX.isLocalMartingale_stochasticIntegral_of_locally_squareIntegrable hF hLX
    (hY.adapted.leftLimitProcess_of_usual hF hY.hasCadlagPaths)
    hY.hasCadlagPaths.hasCagladPaths_leftLimitProcess
  apply (hJY.add hJX hF).congr hF
    (fun t ↦ ((hX.adapted t).mul (hY.adapted t)).sub
      (hX.adapted_quadraticCovariation hY hF t))
  filter_upwards [hX.quadraticCovariation_eq_product_sub_integrals hY hF] with ω hω t
  simp only [Pi.sub_apply, Pi.add_apply, hω t, Pi.mul_apply]
  ring

end ProbabilityTheory
