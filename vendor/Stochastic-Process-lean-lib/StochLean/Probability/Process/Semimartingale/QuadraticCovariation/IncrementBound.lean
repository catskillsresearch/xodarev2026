/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.Semimartingale.QuadraticVariation.Algebra
public import Mathlib.Algebra.QuadraticDiscriminant
public import Mathlib.Topology.Instances.Real.Lemmas

/-! # The pathwise covariation increment bound

One countable intersection handles rational scalar combinations. Continuity
of the scalar polynomial then gives the bound for every real pair of times
on the same event. The discriminant is **nonpositive**; Protter II.25's proof
prints the opposite sign. This is the interval estimate used there, not yet
the weighted total-variation-measure Kunita--Watanabe inequality.
-/

@[expose] public section

open MeasureTheory
open scoped NNReal

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsFiniteMeasure P]
  {F : Filtration ℝ≥0 mΩ} {X Y : ℝ≥0 → Ω → ℝ}

theorem IsSemimartingale.quadraticCovariation_increment_sq_le
    (hX : IsSemimartingale X F P) (hY : IsSemimartingale Y F P) (hF : F.IsUsual P) :
    ∀ᵐ ω ∂P, ∀ s t, s ≤ t →
      (hX.quadraticCovariation hY hF t ω - hX.quadraticCovariation hY hF s ω) ^ 2 ≤
      (hX.quadraticVariation hF t ω - hX.quadraticVariation hF s ω) *
        (hY.quadraticVariation hF t ω - hY.quadraticVariation hF s ω) := by
  have hm : ∀ᵐ ω ∂P, ∀ q : ℚ,
      Monotone (fun t ↦ (hX.add (hY.const_mul (q : ℝ))).quadraticVariation hF t ω) :=
    ae_all_iff.mpr fun q ↦ (hX.add (hY.const_mul (q : ℝ))).hasMonotonePaths_quadraticVariation hF
  have heq : ∀ᵐ ω ∂P, ∀ q : ℚ, ∀ t,
      (hX.add (hY.const_mul (q : ℝ))).quadraticVariation hF t ω =
        hX.quadraticVariation hF t ω + 2 * (q : ℝ) * hX.quadraticCovariation hY hF t ω +
          (q : ℝ) ^ 2 * hY.quadraticVariation hF t ω :=
    ae_all_iff.mpr fun q ↦ hX.quadraticVariation_add_const_mul hY hF (q : ℝ)
  filter_upwards [hm, heq] with ω hmono hformula s t hst
  let a := hY.quadraticVariation hF t ω - hY.quadraticVariation hF s ω
  let b := hX.quadraticCovariation hY hF t ω - hX.quadraticCovariation hY hF s ω
  let c := hX.quadraticVariation hF t ω - hX.quadraticVariation hF s ω
  have hrat (q : ℚ) : 0 ≤ a * ((q : ℝ) * (q : ℝ)) + (2 * b) * (q : ℝ) + c := by
    have h := hmono q hst
    change (hX.add (hY.const_mul (q : ℝ))).quadraticVariation hF s ω ≤
      (hX.add (hY.const_mul (q : ℝ))).quadraticVariation hF t ω at h
    rw [hformula q s, hformula q t] at h
    dsimp only [a, b, c]
    nlinarith only [h]
  have hreal (r : ℝ) : 0 ≤ a * (r * r) + (2 * b) * r + c := by
    refine Rat.denseRange_cast.induction_on r ?_ hrat
    exact isClosed_le continuous_const (by fun_prop)
  have hd := discrim_le_zero hreal
  simp only [discrim] at hd
  change b ^ 2 ≤ c * a
  nlinarith only [hd]

theorem IsSemimartingale.abs_quadraticCovariation_increment_le
    (hX : IsSemimartingale X F P) (hY : IsSemimartingale Y F P) (hF : F.IsUsual P) :
    ∀ᵐ ω ∂P, ∀ s t, s ≤ t →
      |hX.quadraticCovariation hY hF t ω - hX.quadraticCovariation hY hF s ω| ≤
      Real.sqrt (hX.quadraticVariation hF t ω - hX.quadraticVariation hF s ω) *
        Real.sqrt (hY.quadraticVariation hF t ω - hY.quadraticVariation hF s ω) := by
  filter_upwards [hX.quadraticCovariation_increment_sq_le hY hF,
    hX.hasMonotonePaths_quadraticVariation hF] with ω hω hm s t hst
  have hsq := hω s t hst
  have ha : |hX.quadraticCovariation hY hF t ω - hX.quadraticCovariation hY hF s ω| ^ 2 ≤
      (hX.quadraticVariation hF t ω - hX.quadraticVariation hF s ω) *
        (hY.quadraticVariation hF t ω - hY.quadraticVariation hF s ω) := by
    simpa only [sq_abs] using hsq
  simpa only [Real.sqrt_mul (sub_nonneg.mpr (hm hst))] using Real.le_sqrt_of_sq_le ha

theorem IsSemimartingale.quadraticCovariation_eq_of_quadraticVariation_eq
    (hX : IsSemimartingale X F P) (hY : IsSemimartingale Y F P) (hF : F.IsUsual P) :
    ∀ᵐ ω ∂P, ∀ s t, s ≤ t →
      hX.quadraticVariation hF t ω = hX.quadraticVariation hF s ω →
      hX.quadraticCovariation hY hF t ω = hX.quadraticCovariation hY hF s ω := by
  filter_upwards [hX.quadraticCovariation_increment_sq_le hY hF] with ω hω s t hst heq
  have h := hω s t hst
  rw [heq, sub_self, zero_mul] at h
  nlinarith only [h]

end ProbabilityTheory
