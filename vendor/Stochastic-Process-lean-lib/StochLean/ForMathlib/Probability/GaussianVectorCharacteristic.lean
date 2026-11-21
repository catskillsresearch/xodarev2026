/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import Mathlib.Probability.Distributions.Gaussian.Real
public import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic

/-! # The characteristic function of a finite isotropic Gaussian product

The law is Mathlib's product of real Gaussian laws, transported by its
canonical Euclidean-space equivalence. Empty families and zero variance
are included; no covariance invertibility is required.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory WithLp
open scoped NNReal

namespace StochLean

theorem charFun_pi_centered_gaussian {ι : Type*} [Fintype ι]
    (v : ℝ≥0) (u : EuclideanSpace ℝ ι) :
    charFun ((Measure.pi (fun _ : ι ↦ gaussianReal 0 v)).map (toLp 2)) u =
      Complex.exp (Complex.ofReal (-((1 / 2 : ℝ) * (∑ i, (u i) ^ 2)) * (v : ℝ))) := by
  rw [charFun_pi]
  simp_rw [charFun_gaussianReal]
  have he (i : ι) : (u i : ℂ) * 0 * Complex.I - (v : ℂ) * (u i : ℂ) ^ 2 / 2 =
      Complex.ofReal (-((1 / 2 : ℝ) * (u i) ^ 2) * (v : ℝ)) := by
    push_cast
    ring
  simp only [Complex.ofReal_zero]
  simp_rw [he]
  rw [← Complex.exp_sum, ← Complex.ofReal_sum]
  congr 2
  simp only [Finset.sum_mul, Finset.mul_sum, Finset.sum_neg_distrib, neg_mul]

end StochLean
