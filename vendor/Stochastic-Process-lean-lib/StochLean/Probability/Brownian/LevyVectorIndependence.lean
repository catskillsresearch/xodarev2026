/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Brownian.LevyVectorGaussianProcess
public import Mathlib.Probability.Distributions.Gaussian.IsGaussianProcess.Independence

/-! # Independence of entire coordinate processes

Same-time independence first gives zero covariance. Independence of future
increments from the filtration then gives zero cross-coordinate covariance at
arbitrary times. Joint Gaussianity promotes this to independence of the whole
coordinate paths, not just pairwise or same-time independence.
-/

@[expose] public section

open MeasureTheory
open scoped NNReal

namespace ProbabilityTheory

variable {ι Ω : Type*} [Finite ι] {mΩ : MeasurableSpace Ω}
  {P : Measure Ω} [IsProbabilityMeasure P] {F : Filtration ℝ≥0 mΩ}
  {X : ι → ℝ≥0 → Ω → ℝ}
  (hX : ∀ i, IsContinuousLocalMartingale (X i) F P) (hF : F.IsUsual P)
  (hd : ∀ i, Indistinguishable
    (((hX i).isSemimartingale hF).continuousQuadraticVariation hF) (fun t _ ↦ (t : ℝ)) P)
  (ho : ∀ i j, i ≠ j → Indistinguishable
    (((hX i).isSemimartingale hF).continuousQuadraticCovariation
      ((hX j).isSemimartingale hF) hF) 0 P)
  (h0 : ∀ i, ∀ᵐ ω ∂P, X i 0 ω = 0)

include hX hF hd ho h0

theorem covariance_coordinate_time_eq_zero_of_orthogonal
    {i j : ι} (hij : i ≠ j) (s t : ℝ≥0) : cov[X i s, X j t; P] = 0 := by
  have hm (i : ι) (t : ℝ≥0) : MemLp (X i t) 2 P := by
    have hb := (hX i).isBrownianReal_of_continuousBracket_eq_time hF (hd i) (h0 i)
    exact (hb.toIsPreBrownianReal.hasLaw_eval t).hasGaussianLaw.memLp_two
  have hstep (i j : ι) (hij : i ≠ j) (s t : ℝ≥0) (hst : s ≤ t) :
      cov[X i s, X j t; P] = 0 := by
    have heval := (iIndepFun_eval_of_orthogonal hX hF hd ho h0 s).indepFun hij
    have hinc : IndepFun (X i s) (X j t - X j s) P := by
      apply (IndepFun_iff_Indep _ _ _).2
      apply (Indep_iff _ _ _).2
      intro A B hA hB
      exact (Indep_iff _ _ _).1
        ((hX j).indep_increment_past_of_bracket_eq_time hF (hd j) hst) A B
        (((hX i).isSemimartingale hF).adapted s |>.comap_le A hA) hB
    have hx : X j t = X j s + (X j t - X j s) := by
      funext ω
      simp only [Pi.add_apply, Pi.sub_apply]
      ring
    conv_lhs => rw [hx]
    rw [covariance_add_right (hm i s) (hm j s) ((hm j t).sub (hm j s)),
      heval.covariance_eq_zero (hm i s) (hm j s),
      hinc.covariance_eq_zero (hm i s) ((hm j t).sub (hm j s)), zero_add]
  rcases le_total s t with hst | hts
  · exact hstep i j hij s t hst
  · rw [covariance_comm]
    exact hstep j i hij.symm t s hts

theorem iIndepFun_coordinate_processes_of_orthogonal :
    iIndepFun (fun i ω t ↦ X i t ω) P :=
  IsGaussianProcess.iIndepFun_of_covariance_eq_zero
      (isGaussianProcess_coordinate_time_of_orthogonal hX hF hd ho h0)
      (fun i _ ↦ ((hX i).isSemimartingale hF).adapted.measurable.aemeasurable)
      (fun _ _ hij s t ↦ covariance_coordinate_time_eq_zero_of_orthogonal hX hF hd ho h0 hij s t)

end ProbabilityTheory
