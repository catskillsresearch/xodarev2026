/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
import StochLean.Probability.Brownian.QuadraticVariationPaths
import StochLean.Probability.Brownian.IndependentCombination

/-! # Independent Brownian cross variation on one all-times event

Normalize the sum of the two independent Brownian motions, apply the already proved all-times
square-variation theorem, then polarize. The result concerns the entire original partition
sequence and does not introduce a stochastic bracket definition.
-/

open MeasureTheory Filter StochLean
open scoped NNReal Topology

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
  {B C : ℝ≥0 → Ω → ℝ}

/-- Klenke 21.65: independent Brownian processes have zero cross variation, simultaneously
at all times, along every prescribed admissible partition sequence. -/
theorem IsBrownianReal.ae_forall_covariationAlong_restrict_of_indep
    (hB : IsBrownianReal B P) (hC : IsBrownianReal C P)
    (hind : IndepFun (fun ω ↦ (B · ω)) (fun ω ↦ (C · ω)) P)
    {π : ℕ → LocallyFinitePartition} (hπ : IsAdmissiblePartitionSequence π) :
    ∀ᵐ ω ∂P, ∀ T : ℝ≥0,
      HasCovariationAlong (fun n ↦ (π n).restrict T) (B · ω) (C · ω) 0 := by
  have hsqrt : Real.sqrt 2 ≠ 0 := Real.sqrt_ne_zero'.mpr (by norm_num)
  have hc : 2 * ((Real.sqrt 2)⁻¹) ^ 2 = 1 := by
    rw [inv_pow, Real.sq_sqrt (by norm_num)]
    norm_num
  have hsum := hB.add_normalized_of_indep hC hind hc
  filter_upwards [hB.ae_forall_quadraticVariationAlong_restrict hπ,
    hC.ae_forall_quadraticVariationAlong_restrict hπ,
    hsum.ae_forall_quadraticVariationAlong_restrict hπ] with ω hωB hωC hωsum
  intro T
  have hplus : HasQuadraticVariationAlong (fun n ↦ (π n).restrict T)
      ((B · ω) + (C · ω)) (2 * (T : ℝ)) := by
    have h := (hωsum T).const_mul (Real.sqrt 2)
    convert h using 1
    · funext t
      simp only [Pi.add_apply, ← mul_assoc, mul_inv_cancel₀ hsqrt, one_mul]
    · rw [Real.sq_sqrt (by norm_num)]
  have heq : (2 * (T : ℝ) - T - T) / 2 = 0 := by ring
  simpa only [HasCovariationAlong, ← covariationSum_polarization, heq] using
    ((hplus.sub (hωB T)).sub (hωC T)).div_const 2

end ProbabilityTheory
