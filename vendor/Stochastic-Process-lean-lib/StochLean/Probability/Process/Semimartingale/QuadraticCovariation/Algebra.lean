/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.Semimartingale.QuadraticCovariation.Riemann

/-! # Bilinearity and version invariance of the canonical raw covariation

Linearity is inherited from the actual finite increment sums by uniqueness
of UCP limits. All comparisons are on one event for every time.
-/

@[expose] public section

open MeasureTheory
open scoped NNReal

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsFiniteMeasure P]
  {F : Filtration ℝ≥0 mΩ} {X Y Z X' Y' : ℝ≥0 → Ω → ℝ}

theorem IsSemimartingale.quadraticCovariation_self
    (hX : IsSemimartingale X F P) (hF : F.IsUsual P) :
    Indistinguishable (hX.quadraticCovariation hX hF) (hX.quadraticVariation hF) P := by
  apply hX.quadraticCovariation_indistinguishable_of_limits hX hF
  · intro π hπ
    simpa only [StoppingTimePartition.quadraticCovariationSumProcess_self] using
      hX.tendstoUCP_quadraticVariationSumProcess hF hπ
  · exact (hX.hasCadlagPaths_quadraticVariation hF).hasRightContinuousPaths

theorem IsSemimartingale.quadraticCovariation_add_left
    (hX : IsSemimartingale X F P) (hY : IsSemimartingale Y F P)
    (hZ : IsSemimartingale Z F P) (hF : F.IsUsual P) :
    Indistinguishable ((hX.add hY).quadraticCovariation hZ hF)
      (hX.quadraticCovariation hZ hF + hY.quadraticCovariation hZ hF) P := by
  apply (hX.add hY).quadraticCovariation_indistinguishable_of_limits hZ hF
  · intro π hπ
    simpa only [StoppingTimePartition.quadraticCovariationSumProcess_add_left] using
      (hX.tendstoUCP_quadraticCovariationSumProcess hZ hF hπ).add
        (hY.tendstoUCP_quadraticCovariationSumProcess hZ hF hπ)
  · exact ((hX.hasCadlagPaths_quadraticCovariation hZ hF).add
      (hY.hasCadlagPaths_quadraticCovariation hZ hF)).hasRightContinuousPaths

theorem IsSemimartingale.quadraticCovariation_const_mul_left
    (hX : IsSemimartingale X F P) (hY : IsSemimartingale Y F P) (hF : F.IsUsual P)
    (c : ℝ) :
    Indistinguishable ((hX.const_mul c).quadraticCovariation hY hF)
      (c • hX.quadraticCovariation hY hF) P := by
  apply (hX.const_mul c).quadraticCovariation_indistinguishable_of_limits hY hF
  · intro π hπ
    simpa only [StoppingTimePartition.quadraticCovariationSumProcess_const_mul_left] using
      (hX.tendstoUCP_quadraticCovariationSumProcess hY hF hπ).smul c
  · exact ((hX.hasCadlagPaths_quadraticCovariation hY hF).continuous_comp
      (continuous_const.mul continuous_id)).hasRightContinuousPaths

theorem IsSemimartingale.quadraticCovariation_add_right
    (hX : IsSemimartingale X F P) (hY : IsSemimartingale Y F P)
    (hZ : IsSemimartingale Z F P) (hF : F.IsUsual P) :
    Indistinguishable (hX.quadraticCovariation (hY.add hZ) hF)
      (hX.quadraticCovariation hY hF + hX.quadraticCovariation hZ hF) P := by
  filter_upwards [hX.quadraticCovariation_comm (hY.add hZ) hF,
    hY.quadraticCovariation_add_left hZ hX hF,
    hY.quadraticCovariation_comm hX hF, hZ.quadraticCovariation_comm hX hF]
    with ω hsum hadd hy hz t
  simp only [hsum t, hadd t, Pi.add_apply, hy t, hz t]

theorem IsSemimartingale.quadraticCovariation_const_mul_right
    (hX : IsSemimartingale X F P) (hY : IsSemimartingale Y F P) (hF : F.IsUsual P)
    (c : ℝ) :
    Indistinguishable (hX.quadraticCovariation (hY.const_mul c) hF)
      (c • hX.quadraticCovariation hY hF) P := by
  filter_upwards [hX.quadraticCovariation_comm (hY.const_mul c) hF,
    hY.quadraticCovariation_const_mul_left hX hF c, hY.quadraticCovariation_comm hX hF]
    with ω hcomm hmul hxy t
  simp only [hcomm t, hmul t, Pi.smul_apply, smul_eq_mul, hxy t]

theorem IsSemimartingale.quadraticCovariation_congr
    (hX : IsSemimartingale X F P) (hY : IsSemimartingale Y F P)
    (hX' : IsSemimartingale X' F P) (hY' : IsSemimartingale Y' F P) (hF : F.IsUsual P)
    (hXX' : Indistinguishable X X' P) (hYY' : Indistinguishable Y Y' P) :
    Indistinguishable (hX.quadraticCovariation hY hF) (hX'.quadraticCovariation hY' hF) P := by
  have hsum : Indistinguishable (X + Y) (X' + Y') P := by
    filter_upwards [hXX', hYY'] with ω hx hy t
    simp only [Pi.add_apply, hx t, hy t]
  filter_upwards [(hX.add hY).quadraticVariation_congr (hX'.add hY') hF hsum,
    hX.quadraticVariation_congr hX' hF hXX', hY.quadraticVariation_congr hY' hF hYY']
    with ω hsumω hx hy t
  simp only [quadraticCovariation, hsumω t, hx t, hy t]

end ProbabilityTheory
