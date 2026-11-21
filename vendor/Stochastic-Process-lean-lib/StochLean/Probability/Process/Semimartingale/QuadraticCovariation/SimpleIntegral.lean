/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.Semimartingale.SimplePredictable.CrossSumsConvergence
public import StochLean.Probability.Process.Semimartingale.QuadraticCovariation.IntegralContinuity

/-! # The simple-integrand case of Protter II.29

Actual finite-sum limits identify the bracket. A simple representation is used
only in the proof; the public statement compares existing canonical integrals.
-/

@[expose] public section

open MeasureTheory
open scoped NNReal

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsFiniteMeasure P]
  {F : Filtration ℝ≥0 mΩ} {X Y H : ℝ≥0 → Ω → ℝ}

theorem IsSemimartingale.quadraticCovariation_stochasticIntegral_of_simple
    (hX : IsSemimartingale X F P) (hY : IsSemimartingale Y F P) (hF : F.IsUsual P)
    (ha : Adapted F H) (hr : HasCagladPaths H P) (hH : IsSimplePredictable H F) :
    Indistinguishable
      ((hX.isSemimartingale_stochasticIntegral hF ha hr).quadraticCovariation hY hF)
      ((hX.isSemimartingale_quadraticCovariation hY hF).stochasticIntegral hF ha hr) P := by
  obtain ⟨R, hR⟩ := hH
  have hH : IsSimplePredictable H F := ⟨R, hR⟩
  let hJ := hX.isSemimartingale_stochasticIntegral hF ha hr
  let hB := hX.isSemimartingale_quadraticCovariation hY hF
  have helem := hH.elementaryIntegralProcess_eq R hR X
  have hJE : Indistinguishable (hX.stochasticIntegral hF ha hr) (R.integralProcess X) P := by
    simpa only [helem] using hX.stochasticIntegral_indistinguishable_of_simple hF ha hr hH
  have hE := hJ.congr_of_adapted hJE
    (R.adapted_integralProcess hX.adapted hF hX.hasCadlagPaths.hasRightContinuousPaths)
  have hEB : Indistinguishable (hE.quadraticCovariation hY hF)
      (R.integralProcess (hX.quadraticCovariation hY hF)) P :=
    hE.quadraticCovariation_indistinguishable_of_limits hY hF
      (fun _ hπ ↦ R.tendstoUCP_quadraticCovariationSum_integralProcess hX hY hF hπ)
      (R.hasCadlagPaths_integralProcess hB.hasCadlagPaths).hasRightContinuousPaths
  have hBE : Indistinguishable (hB.stochasticIntegral hF ha hr)
      (R.integralProcess (hX.quadraticCovariation hY hF)) P := by
    simpa only [hH.elementaryIntegralProcess_eq R hR (hX.quadraticCovariation hY hF)] using
      hB.stochasticIntegral_indistinguishable_of_simple hF ha hr hH
  exact (hJ.quadraticCovariation_congr hY hE hY hF hJE
    (ae_of_all _ fun _ _ ↦ rfl)).trans (hEB.trans hBE.symm)

end ProbabilityTheory
