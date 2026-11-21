/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.Semimartingale.StochasticExponential.Basic
public import StochLean.Analysis.PathVariation.ExponentialJumpProduct

/-! # Equivalent raw/continuous formulas and the exact zero-jump criterion

Both actual products converge. A zero of the product is equivalent to an
actual jump of size -1; convergence to zero without such a factor is excluded
by the proved absolute summability of deviations from one.
-/

@[expose] public section

open MeasureTheory Set StochLean
open scoped NNReal

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsFiniteMeasure P]
  {F : Filtration ℝ≥0 mΩ} {X : ℝ≥0 → Ω → ℝ}

theorem IsSemimartingale.multipliable_stochasticExponential_raw_product
    (hX : IsSemimartingale X F P) (hF : F.IsUsual P) :
    ∀ᵐ ω ∂P, ∀ t : ℝ≥0, Multipliable (fun s : Ioc 0 t ↦
      (1 + jumpProcess X s ω) *
        Real.exp (-jumpProcess X s ω + (1 / 2 : ℝ) * jumpProcess X s ω ^ 2)) := by
  filter_upwards [hX.summable_sq_jumps hF] with ω hs t
  exact multipliable_compensatedExponentialJumpFactor (hs t)

theorem IsSemimartingale.stochasticExponential_ne_zero_iff
    (hX : IsSemimartingale X F P) (hF : F.IsUsual P) :
    ∀ᵐ ω ∂P, ∀ t : ℝ≥0, hX.stochasticExponential hF t ω ≠ 0 ↔
      ∀ s : Ioc 0 t, jumpProcess X s ω ≠ -1 := by
  filter_upwards [hX.summable_sq_jumps hF] with ω hs t
  rw [stochasticExponential, mul_ne_zero_iff]
  have hp := tprod_exponentialJumpFactor_ne_zero_iff (hs t)
  exact ⟨fun h ↦ hp.mp h.2, fun h ↦ ⟨Real.exp_ne_zero _, hp.mpr h⟩⟩

theorem IsSemimartingale.stochasticExponential_raw_formula
    (hX : IsSemimartingale X F P) (hF : F.IsUsual P) (h0 : X 0 =ᵐ[P] 0) :
    Indistinguishable (hX.stochasticExponential hF) (fun t ω ↦
      Real.exp (X t ω - (1 / 2 : ℝ) * hX.quadraticVariation hF t ω) *
        ∏' s : Ioc 0 t, (1 + jumpProcess X s ω) *
          Real.exp (-jumpProcess X s ω + (1 / 2 : ℝ) * jumpProcess X s ω ^ 2)) P := by
  filter_upwards [hX.quadraticVariation_continuous_jump_decomposition hF, h0]
    with ω hq hz t
  have hp := tprod_compensatedExponentialJumpFactor (hq t).1
  have hq' := (hq t).2
  simp only [hz, Pi.zero_apply, zero_pow (by decide : 2 ≠ 0), zero_add] at hq'
  have he : X t ω - (1 / 2 : ℝ) * hX.continuousQuadraticVariation hF t ω =
      (X t ω - (1 / 2 : ℝ) * hX.quadraticVariation hF t ω) +
        (1 / 2 : ℝ) * ∑' s : Ioc 0 t, jumpProcess X s ω ^ 2 := by
    linarith only [hq']
  rw [hp]
  simp only [stochasticExponential, stochasticExponentialJumpProduct, he, Real.exp_add]
  ring

end ProbabilityTheory
