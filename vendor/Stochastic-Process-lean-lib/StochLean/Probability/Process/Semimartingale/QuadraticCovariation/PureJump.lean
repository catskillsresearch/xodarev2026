/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.Semimartingale.QuadraticVariation.PureJump
public import StochLean.Probability.Process.Semimartingale.QuadraticVariation.ContinuousPartQuadraticAlgebra
public import StochLean.ForMathlib.Analysis.AffineNonnegative

/-! # Mixed covariation of a quadratic pure-jump semimartingale

Protter II.28, with the library's raw initial-product convention. Positivity
of the continuous square bracket for all integer linear combinations forces
the continuous mixed bracket to vanish when either diagonal vanishes. The
countable intersection is taken before choosing a path or a time. The jump
series is the actual absolutely summable series, not a new bracket owner.
-/

@[expose] public section

open MeasureTheory StochLean Set
open scoped NNReal

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsFiniteMeasure P]
  {F : Filtration ℝ≥0 mΩ} {X Y : ℝ≥0 → Ω → ℝ}

theorem IsSemimartingale.continuousQuadraticCovariation_zero_on_left_zero_paths
    (hX : IsSemimartingale X F P) (hY : IsSemimartingale Y F P) (hF : F.IsUsual P) :
    ∀ᵐ ω ∂P, (∀ t, hX.continuousQuadraticVariation hF t ω = 0) →
      ∀ t, hX.continuousQuadraticCovariation hY hF t ω = 0 := by
  have hall : ∀ᵐ ω ∂P, ∀ z : ℤ, ∀ t,
      (hY.add (hX.const_mul (z : ℝ))).continuousQuadraticVariation hF t ω =
        hY.continuousQuadraticVariation hF t ω +
          2 * (z : ℝ) * hY.continuousQuadraticCovariation hX hF t ω +
          (z : ℝ) ^ 2 * hX.continuousQuadraticVariation hF t ω :=
    ae_all_iff.mpr fun z ↦ hY.continuousQuadraticVariation_add_const_mul hX hF (z : ℝ)
  filter_upwards [hall, hX.continuousQuadraticCovariation_comm hY hF]
    with ω ha hcomm hx t
  have hz : 2 * hY.continuousQuadraticCovariation hX hF t ω = 0 := by
    apply eq_zero_of_forall_int_affine_nonneg
      (a := hY.continuousQuadraticVariation hF t ω)
    intro z
    have hp := (hY.add (hX.const_mul (z : ℝ))).continuousQuadraticVariation_nonneg hF t ω
    rw [ha z t, hx t, mul_zero, add_zero] at hp
    nlinarith only [hp]
  rw [hcomm t]
  linarith

theorem IsSemimartingale.continuousQuadraticCovariation_zero_of_quadraticPureJump_left
    (hX : IsSemimartingale X F P) (hY : IsSemimartingale Y F P) (hF : F.IsUsual P)
    (hQ : hX.IsQuadraticPureJump hF) :
    Indistinguishable (hX.continuousQuadraticCovariation hY hF) 0 P := by
  filter_upwards [hX.continuousQuadraticCovariation_zero_on_left_zero_paths hY hF, hQ]
    with ω hz hx t
  exact hz hx t

theorem IsSemimartingale.continuousQuadraticCovariation_zero_of_quadraticPureJump_right
    (hX : IsSemimartingale X F P) (hY : IsSemimartingale Y F P) (hF : F.IsUsual P)
    (hQ : hY.IsQuadraticPureJump hF) :
    Indistinguishable (hX.continuousQuadraticCovariation hY hF) 0 P :=
  (hX.continuousQuadraticCovariation_comm hY hF).trans
    (hY.continuousQuadraticCovariation_zero_of_quadraticPureJump_left hX hF hQ)

theorem IsSemimartingale.quadraticCovariation_of_quadraticPureJump_left
    (hX : IsSemimartingale X F P) (hY : IsSemimartingale Y F P) (hF : F.IsUsual P)
    (hQ : hX.IsQuadraticPureJump hF) :
    Indistinguishable (hX.quadraticCovariation hY hF)
      (fun t ω ↦ X 0 ω * Y 0 ω +
        ∑' s : Ioc 0 t, jumpProcess X s ω * jumpProcess Y s ω) P := by
  filter_upwards [hX.quadraticCovariation_continuous_jump_decomposition hY hF,
    hX.continuousQuadraticCovariation_zero_of_quadraticPureJump_left hY hF hQ]
    with ω hd hz t
  simpa only [hz t, Pi.zero_apply, add_zero] using (hd t).2

theorem IsSemimartingale.quadraticCovariation_of_quadraticPureJump_right
    (hX : IsSemimartingale X F P) (hY : IsSemimartingale Y F P) (hF : F.IsUsual P)
    (hQ : hY.IsQuadraticPureJump hF) :
    Indistinguishable (hX.quadraticCovariation hY hF)
      (fun t ω ↦ X 0 ω * Y 0 ω +
        ∑' s : Ioc 0 t, jumpProcess X s ω * jumpProcess Y s ω) P := by
  filter_upwards [hX.quadraticCovariation_continuous_jump_decomposition hY hF,
    hX.continuousQuadraticCovariation_zero_of_quadraticPureJump_right hY hF hQ]
    with ω hd hz t
  simpa only [hz t, Pi.zero_apply, add_zero] using (hd t).2

theorem IsSemimartingale.quadraticCovariation_of_finiteVariation_left
    (hX : IsSemimartingale X F P) (hY : IsSemimartingale Y F P) (hF : F.IsUsual P)
    (hv : HasFiniteVariationPaths X P) :
    Indistinguishable (hX.quadraticCovariation hY hF)
      (fun t ω ↦ X 0 ω * Y 0 ω +
        ∑' s : Ioc 0 t, jumpProcess X s ω * jumpProcess Y s ω) P :=
  hX.quadraticCovariation_of_quadraticPureJump_left hY hF
    (hX.isQuadraticPureJump_of_finiteVariation hF hv)

theorem IsSemimartingale.quadraticCovariation_of_finiteVariation_right
    (hX : IsSemimartingale X F P) (hY : IsSemimartingale Y F P) (hF : F.IsUsual P)
    (hv : HasFiniteVariationPaths Y P) :
    Indistinguishable (hX.quadraticCovariation hY hF)
      (fun t ω ↦ X 0 ω * Y 0 ω +
        ∑' s : Ioc 0 t, jumpProcess X s ω * jumpProcess Y s ω) P :=
  hX.quadraticCovariation_of_quadraticPureJump_right hY hF
    (hY.isQuadraticPureJump_of_finiteVariation hF hv)

theorem IsSemimartingale.quadraticCovariation_initial_of_quadraticPureJump_continuous
    (hX : IsSemimartingale X F P) (hY : IsSemimartingale Y F P) (hF : F.IsUsual P)
    (hQ : hX.IsQuadraticPureJump hF) (hc : HasContinuousPaths Y P) :
    Indistinguishable (hX.quadraticCovariation hY hF)
      (fun _ ω ↦ X 0 ω * Y 0 ω) P := by
  filter_upwards [hX.quadraticCovariation_of_quadraticPureJump_left hY hF hQ, hc]
    with ω he hy t
  rw [he t]
  have hz : (∑' s : Ioc 0 t, jumpProcess X s ω * jumpProcess Y s ω) = 0 := by
    calc
      _ = ∑' _s : Ioc 0 t, (0 : ℝ) := by
        apply tsum_congr
        intro s
        rw [hy.jumpProcess_eq_zero (ne_of_gt s.property.1), mul_zero]
      _ = 0 := tsum_zero
  exact (congrArg (X 0 ω * Y 0 ω + ·) hz).trans (add_zero _)

theorem IsSemimartingale.quadraticCovariation_initial_of_continuous_quadraticPureJump
    (hX : IsSemimartingale X F P) (hY : IsSemimartingale Y F P) (hF : F.IsUsual P)
    (hc : HasContinuousPaths X P) (hQ : hY.IsQuadraticPureJump hF) :
    Indistinguishable (hX.quadraticCovariation hY hF)
      (fun _ ω ↦ X 0 ω * Y 0 ω) P := by
  filter_upwards [hX.quadraticCovariation_of_quadraticPureJump_right hY hF hQ, hc]
    with ω he hx t
  rw [he t]
  have hz : (∑' s : Ioc 0 t, jumpProcess X s ω * jumpProcess Y s ω) = 0 := by
    calc
      _ = ∑' _s : Ioc 0 t, (0 : ℝ) := by
        apply tsum_congr
        intro s
        rw [hx.jumpProcess_eq_zero (ne_of_gt s.property.1), zero_mul]
      _ = 0 := tsum_zero
  exact (congrArg (X 0 ω * Y 0 ω + ·) hz).trans (add_zero _)

theorem IsSemimartingale.quadraticCovariation_initial_of_continuous_finiteVariation_left
    (hX : IsSemimartingale X F P) (hY : IsSemimartingale Y F P) (hF : F.IsUsual P)
    (hc : HasContinuousPaths X P) (hv : HasFiniteVariationPaths X P) :
    Indistinguishable (hX.quadraticCovariation hY hF)
      (fun _ ω ↦ X 0 ω * Y 0 ω) P := by
  filter_upwards [hX.quadraticCovariation_of_finiteVariation_left hY hF hv, hc]
    with ω he hx t
  rw [he t]
  have hz : (∑' s : Ioc 0 t, jumpProcess X s ω * jumpProcess Y s ω) = 0 := by
    calc
      _ = ∑' _s : Ioc 0 t, (0 : ℝ) := by
        apply tsum_congr
        intro s
        rw [hx.jumpProcess_eq_zero (ne_of_gt s.property.1), zero_mul]
      _ = 0 := tsum_zero
  exact (congrArg (X 0 ω * Y 0 ω + ·) hz).trans (add_zero _)

theorem IsSemimartingale.quadraticCovariation_initial_of_continuous_finiteVariation_right
    (hX : IsSemimartingale X F P) (hY : IsSemimartingale Y F P) (hF : F.IsUsual P)
    (hc : HasContinuousPaths Y P) (hv : HasFiniteVariationPaths Y P) :
    Indistinguishable (hX.quadraticCovariation hY hF)
      (fun _ ω ↦ X 0 ω * Y 0 ω) P := by
  filter_upwards [hX.quadraticCovariation_comm hY hF,
    hY.quadraticCovariation_initial_of_continuous_finiteVariation_left hX hF hc hv]
    with ω hcomm hy t
  exact (hcomm t).trans ((hy t).trans (mul_comm _ _))

end ProbabilityTheory
