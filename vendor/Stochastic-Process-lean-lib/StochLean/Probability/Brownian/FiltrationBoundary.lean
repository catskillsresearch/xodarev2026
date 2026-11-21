/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Brownian.Martingale

/-! # Full information destroys the Brownian martingale property

This boundary theorem explains why Levy's filtered equivalence retains
independence from the specified past. It applies to every Brownian law,
not just to a finite toy filtration.
-/

@[expose] public section

open MeasureTheory
open scoped NNReal

namespace ProbabilityTheory

theorem IsPreBrownianReal.not_martingale_fullInformation
    {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
    {B : ℝ≥0 → Ω → ℝ} (hB : IsPreBrownianReal B P) :
    ¬ Martingale B (Filtration.const ℝ≥0 mΩ le_rfl) P := by
  intro hM
  have h := hM.condExp_ae_eq (show (0 : ℝ≥0) ≤ 1 from zero_le)
  change P[B 1 | mΩ] =ᵐ[P] B 0 at h
  rw [condExp_of_stronglyMeasurable (μ := P) (m := mΩ) le_rfl
    (hM.stronglyAdapted 1) (hM.integrable 1)] at h
  have hz : B 1 =ᵐ[P] 0 := h.trans hB.eval_zero_ae_eq_zero
  have hs : (∫ ω, (B 1 ω) ^ 2 ∂P) = 0 := by
    calc
      _ = ∫ _ : Ω, (0 : ℝ) ∂P := integral_congr_ae (hz.mono fun _ hω ↦ by simp [hω])
      _ = 0 := integral_zero _ _
  have h1 := hB.integral_eval_sq 1
  rw [hs] at h1
  norm_num at h1

end ProbabilityTheory
