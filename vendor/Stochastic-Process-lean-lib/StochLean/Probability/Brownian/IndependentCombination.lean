/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import Mathlib.Probability.BrownianMotion.Basic
public import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Basic
public import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Independence
public import Mathlib.Probability.Distributions.Gaussian.IsGaussianProcess.Basic

/-! # Normalized sums of independent Brownian processes

Independence is imposed on the processes, not merely on their equal-time marginals. Finite
restrictions give joint Gaussian laws; all cross covariances vanish by process independence.
-/

@[expose] public section

open MeasureTheory
open scoped NNReal ProbabilityTheory

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
  {B C : ℝ≥0 → Ω → ℝ}

theorem IsPreBrownianReal.isGaussianProcess_add_of_indep
    (hB : IsPreBrownianReal B P) (hC : IsPreBrownianReal C P)
    (hind : IndepFun (fun ω ↦ (B · ω)) (fun ω ↦ (C · ω)) P) :
    IsGaussianProcess (fun t ω ↦ B t ω + C t ω) P where
  hasGaussianLaw I := by
    have hi := hind.comp (Finset.measurable_restrict I) (Finset.measurable_restrict I)
    exact (hi.hasGaussianLaw (hB.hasLaw I).hasGaussianLaw (hC.hasLaw I).hasGaussianLaw).add

theorem IsPreBrownianReal.add_normalized_of_indep
    (hB : IsPreBrownianReal B P) (hC : IsPreBrownianReal C P)
    (hind : IndepFun (fun ω ↦ (B · ω)) (fun ω ↦ (C · ω)) P)
    {c : ℝ} (hc : 2 * c ^ 2 = 1) :
    IsPreBrownianReal (fun t ω ↦ c * (B t ω + C t ω)) P := by
  let : IsProbabilityMeasure P := (hB.hasLaw_eval 0).isProbabilityMeasure
  have hG := (hB.isGaussianProcess_add_of_indep hC hind).smul (fun _ ↦ c)
  apply hG.isPreBrownianReal_of_covariance
  · intro t
    simp only [smul_eq_mul]
    rw [integral_const_mul, integral_add (hB.integrable_eval t) (hC.integrable_eval t),
      hB.integral_eval, hC.integral_eval]
    ring
  · intro s t hst
    have hBlp (u : ℝ≥0) := (hB.hasLaw_eval u).hasGaussianLaw.memLp_two
    have hClp (u : ℝ≥0) := (hC.hasLaw_eval u).hasGaussianLaw.memLp_two
    have hBC : cov[B s, C t; P] = 0 :=
      (hind.comp (measurable_pi_apply s) (measurable_pi_apply t)).covariance_eq_zero
        (hBlp s) (hClp t)
    have hCB : cov[C s, B t; P] = 0 :=
      (hind.symm.comp (measurable_pi_apply s) (measurable_pi_apply t)).covariance_eq_zero
        (hClp s) (hBlp t)
    have hcov : cov[B s + C s, B t + C t; P] = 2 * (s : ℝ) := by
      rw [covariance_add_left (hBlp s) (hClp s) ((hBlp t).add (hClp t)),
        covariance_add_right (hBlp s) (hBlp t) (hClp t),
        covariance_add_right (hClp s) (hBlp t) (hClp t), hBC, hCB,
        hB.covariance_eval, hC.covariance_eval, min_eq_left hst]
      ring
    change cov[fun ω ↦ c * (B s ω + C s ω), fun ω ↦ c * (B t ω + C t ω); P] = s
    rw [covariance_const_mul_left, covariance_const_mul_right]
    change c * (c * cov[B s + C s, B t + C t; P]) = s
    rw [hcov]
    calc
      c * (c * (2 * (s : ℝ))) = (2 * c ^ 2) * s := by ring
      _ = s := by rw [hc, one_mul]

theorem IsBrownianReal.add_normalized_of_indep
    (hB : IsBrownianReal B P) (hC : IsBrownianReal C P)
    (hind : IndepFun (fun ω ↦ (B · ω)) (fun ω ↦ (C · ω)) P)
    {c : ℝ} (hc : 2 * c ^ 2 = 1) :
    IsBrownianReal (fun t ω ↦ c * (B t ω + C t ω)) P := by
  refine ⟨hB.toIsPreBrownianReal.add_normalized_of_indep hC.toIsPreBrownianReal hind hc, ?_⟩
  filter_upwards [hB.cont, hC.cont] with ω hωB hωC
  exact continuous_const.mul (hωB.add hωC)

end ProbabilityTheory
