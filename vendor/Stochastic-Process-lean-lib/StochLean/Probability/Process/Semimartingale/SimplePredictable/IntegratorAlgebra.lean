/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.Semimartingale.SimplePredictable

/-! # Elementary linearity in the integrator

These declarations retain their original public names and statements. They live below
good-integrator stability so that the source simple-process algebra can reuse them directly.
-/

@[expose] public section

open MeasureTheory Finset
open scoped NNReal

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {F : Filtration ℝ≥0 mΩ}

theorem SimplePredictableRep.integral_add_integrator (H : SimplePredictableRep F)
    (X Y : ℝ≥0 → Ω → ℝ) : H.integral (X + Y) = H.integral X + H.integral Y := by
  funext ω
  simp only [SimplePredictableRep.integral, Pi.add_apply, add_sub_add_comm,
    mul_add, sum_add_distrib]
  ring

theorem SimplePredictableRep.integral_const_mul_integrator (H : SimplePredictableRep F)
    (c : ℝ) (X : ℝ≥0 → Ω → ℝ) :
    H.integral (fun t ω ↦ c * X t ω) = fun ω ↦ c * H.integral X ω := by
  funext ω
  unfold SimplePredictableRep.integral
  have hsum : (∑ i, H.coefficient i ω *
      (c * X (H.partition.point i.succ ω) ω - c * X (H.partition.point i.castSucc ω) ω)) =
      c * ∑ i, H.coefficient i ω *
        (X (H.partition.point i.succ ω) ω - X (H.partition.point i.castSucc ω) ω) := by
    rw [mul_sum]
    apply sum_congr rfl
    intro i _
    ring
  rw [hsum]
  ring

theorem IsSimplePredictable.elementaryIntegral_add_integrator
    {H : ℝ≥0 → Ω → ℝ} (hH : IsSimplePredictable H F) (X Y : ℝ≥0 → Ω → ℝ) :
    hH.elementaryIntegral (X + Y) = hH.elementaryIntegral X + hH.elementaryIntegral Y :=
  hH.choose.integral_add_integrator X Y

theorem IsSimplePredictable.elementaryIntegral_const_mul_integrator
    {H : ℝ≥0 → Ω → ℝ} (hH : IsSimplePredictable H F) (c : ℝ) (X : ℝ≥0 → Ω → ℝ) :
    hH.elementaryIntegral (fun t ω ↦ c * X t ω) = fun ω ↦ c * hH.elementaryIntegral X ω :=
  hH.choose.integral_const_mul_integrator c X

end ProbabilityTheory
