/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.Semimartingale.QuadraticVariation.Increasing
public import StochLean.Probability.Process.Semimartingale.Subtraction
public import StochLean.ForMathlib.VariationAlgebra

/-! # Raw quadratic covariation by polarization of the canonical square bracket

This is the design's sole mixed bracket owner. It retains `X₀ Y₀`, is adapted
and cadlag, and has locally finite-variation paths. It is not asserted to be
increasing and is not a predictable compensator bracket.
-/

@[expose] public section

open MeasureTheory Set
open scoped NNReal

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsFiniteMeasure P]
  {F : Filtration ℝ≥0 mΩ} {X Y : ℝ≥0 → Ω → ℝ}

noncomputable def IsSemimartingale.quadraticCovariation
    (hX : IsSemimartingale X F P) (hY : IsSemimartingale Y F P) (hF : F.IsUsual P) :
    ℝ≥0 → Ω → ℝ := fun t ω ↦ (1 / 2 : ℝ) *
      ((hX.add hY).quadraticVariation hF t ω - hX.quadraticVariation hF t ω -
        hY.quadraticVariation hF t ω)

theorem IsSemimartingale.quadraticCovariation_proof_irrel
    (hX hX' : IsSemimartingale X F P) (hY hY' : IsSemimartingale Y F P)
    (hF hF' : F.IsUsual P) :
    hX.quadraticCovariation hY hF = hX'.quadraticCovariation hY' hF' := rfl

theorem IsSemimartingale.adapted_quadraticCovariation
    (hX : IsSemimartingale X F P) (hY : IsSemimartingale Y F P) (hF : F.IsUsual P) :
    Adapted F (hX.quadraticCovariation hY hF) := fun t ↦
  ((((hX.add hY).adapted_quadraticVariation hF t).sub (hX.adapted_quadraticVariation hF t)).sub
    (hY.adapted_quadraticVariation hF t)).const_mul (1 / 2)

theorem IsSemimartingale.hasCadlagPaths_quadraticCovariation
    (hX : IsSemimartingale X F P) (hY : IsSemimartingale Y F P) (hF : F.IsUsual P) :
    HasCadlagPaths (hX.quadraticCovariation hY hF) P := by
  have hq := ((((hX.add hY).hasCadlagPaths_quadraticVariation hF).sub
    (hX.hasCadlagPaths_quadraticVariation hF)).sub (hY.hasCadlagPaths_quadraticVariation hF))
  exact hq.continuous_comp (continuous_const.mul continuous_id)

theorem IsSemimartingale.quadraticCovariation_zero_ae
    (hX : IsSemimartingale X F P) (hY : IsSemimartingale Y F P) (hF : F.IsUsual P) :
    hX.quadraticCovariation hY hF 0 =ᵐ[P] fun ω ↦ X 0 ω * Y 0 ω := by
  filter_upwards [(hX.add hY).quadraticVariation_zero_ae hF,
    hX.quadraticVariation_zero_ae hF, hY.quadraticVariation_zero_ae hF] with ω hsum hx hy
  simp only [quadraticCovariation, hsum, hx, hy, Pi.add_apply]
  ring

theorem IsSemimartingale.quadraticCovariation_comm
    (hX : IsSemimartingale X F P) (hY : IsSemimartingale Y F P) (hF : F.IsUsual P) :
    Indistinguishable (hX.quadraticCovariation hY hF) (hY.quadraticCovariation hX hF) P := by
  have heq : Indistinguishable (X + Y) (Y + X) P :=
    ae_of_all _ fun ω t ↦ add_comm (X t ω) (Y t ω)
  filter_upwards [(hX.add hY).quadraticVariation_congr (hY.add hX) hF heq] with ω hω t
  simp only [quadraticCovariation, hω t]
  ring

theorem IsSemimartingale.hasFiniteVariationPaths_quadraticCovariation
    (hX : IsSemimartingale X F P) (hY : IsSemimartingale Y F P) (hF : F.IsUsual P) :
    HasFiniteVariationPaths (hX.quadraticCovariation hY hF) P := by
  filter_upwards [(hX.add hY).hasMonotonePaths_quadraticVariation hF,
    hX.hasMonotonePaths_quadraticVariation hF, hY.hasMonotonePaths_quadraticVariation hF]
    with ω hsum hx hy
  have hhalf {f : ℝ≥0 → ℝ} (hf : Monotone f) : Monotone (fun t ↦ (1 / 2 : ℝ) * f t) :=
    fun _ _ hst ↦ mul_le_mul_of_nonneg_left (hf hst) (by norm_num)
  have hv := StochLean.locallyBoundedVariationOn_sub
    (StochLean.locallyBoundedVariationOn_sub
      ((hhalf hsum).monotoneOn univ).locallyBoundedVariationOn
      ((hhalf hx).monotoneOn univ).locallyBoundedVariationOn)
    ((hhalf hy).monotoneOn univ).locallyBoundedVariationOn
  convert! hv using 1
  funext t
  dsimp only [quadraticCovariation]
  ring

theorem IsSemimartingale.isSemimartingale_quadraticCovariation
    (hX : IsSemimartingale X F P) (hY : IsSemimartingale Y F P) (hF : F.IsUsual P) :
    IsSemimartingale (hX.quadraticCovariation hY hF) F P :=
  (hX.hasFiniteVariationPaths_quadraticCovariation hY hF).isSemimartingale
    (hX.adapted_quadraticCovariation hY hF) hF (hX.hasCadlagPaths_quadraticCovariation hY hF)

end ProbabilityTheory
