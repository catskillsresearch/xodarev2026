/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Analysis.PathVariation.Basic

/-! # Polarization and algebra of deterministic limiting covariation -/

@[expose] public section

open Filter Finset
open scoped NNReal Topology

namespace StochLean

variable {T : ℝ≥0} {π : ℕ → TimePartition T} {f g h : ℝ≥0 → ℝ} {a b c : ℝ}

theorem TimePartition.increment_sub (ρ : TimePartition T) (f g : ℝ≥0 → ℝ)
    (i : Fin ρ.size) : ρ.increment (f - g) i = ρ.increment f i - ρ.increment g i := by
  simp only [TimePartition.increment, Pi.sub_apply]
  ring

theorem quadraticVariationSum_mul (ρ : TimePartition T) (c : ℝ) (f : ℝ≥0 → ℝ) :
    quadraticVariationSum ρ (fun t ↦ c * f t) = c ^ 2 * quadraticVariationSum ρ f := by
  simp only [quadraticVariationSum, TimePartition.increment_mul, mul_pow, mul_sum]

theorem quadraticVariationSum_sub (ρ : TimePartition T) (f g : ℝ≥0 → ℝ) :
    quadraticVariationSum ρ (f - g) = quadraticVariationSum ρ f +
      quadraticVariationSum ρ g - 2 * covariationSum ρ f g := by
  simp only [quadraticVariationSum, covariationSum, TimePartition.increment_sub,
    mul_sum, ← sum_add_distrib, ← sum_sub_distrib]
  apply sum_congr rfl
  intro i _
  ring

/-- The source polarization form does not presume the individual square variations exist. -/
theorem covariationSum_polarization_sub (ρ : TimePartition T) (f g : ℝ≥0 → ℝ) :
    covariationSum ρ f g =
      (quadraticVariationSum ρ (f + g) - quadraticVariationSum ρ (f - g)) / 4 := by
  rw [quadraticVariationSum_add, quadraticVariationSum_sub]
  ring

theorem HasCovariationAlong.comm (hfg : HasCovariationAlong π f g a) :
    HasCovariationAlong π g f a := by
  simpa only [HasCovariationAlong, covariationSum_comm] using hfg

theorem HasCovariationAlong.add_left (hfg : HasCovariationAlong π f h a)
    (hgg : HasCovariationAlong π g h b) : HasCovariationAlong π (f + g) h (a + b) := by
  simpa only [HasCovariationAlong, ← covariationSum_add_left] using hfg.add hgg

theorem HasCovariationAlong.const_mul_left (hfg : HasCovariationAlong π f g a) (c : ℝ) :
    HasCovariationAlong π (fun t ↦ c * f t) g (c * a) := by
  simpa only [HasCovariationAlong, ← covariationSum_mul_left] using hfg.const_mul c

theorem HasQuadraticVariationAlong.const_mul (hf : HasQuadraticVariationAlong π f a) (c : ℝ) :
    HasQuadraticVariationAlong π (fun t ↦ c * f t) (c ^ 2 * a) := by
  simpa only [HasQuadraticVariationAlong, quadraticVariationSum_mul] using
    (Filter.Tendsto.const_mul (c ^ 2) (show Tendsto _ _ _ from hf))

theorem HasQuadraticVariationAlong.polarization_sub
    (hplus : HasQuadraticVariationAlong π (f + g) a)
    (hminus : HasQuadraticVariationAlong π (f - g) b) :
    HasCovariationAlong π f g ((a - b) / 4) := by
  simpa only [HasCovariationAlong, ← covariationSum_polarization_sub] using
    (hplus.sub hminus).div_const 4

theorem HasQuadraticVariationAlong.add_of_covariation
    (hf : HasQuadraticVariationAlong π f a) (hg : HasQuadraticVariationAlong π g b)
    (hfg : HasCovariationAlong π f g c) :
    HasQuadraticVariationAlong π (f + g) (a + b + 2 * c) := by
  simpa only [HasQuadraticVariationAlong, quadraticVariationSum_add] using
    (hf.add hg).add (hfg.const_mul 2)

theorem HasCovariationAlong.abs_le_sqrt (hfg : HasCovariationAlong π f g c)
    (hf : HasQuadraticVariationAlong π f a) (hg : HasQuadraticVariationAlong π g b) :
    |c| ≤ Real.sqrt a * Real.sqrt b := by
  exact le_of_tendsto_of_tendsto' hfg.abs
    ((Real.continuous_sqrt.continuousAt.tendsto.comp hf).mul
      (Real.continuous_sqrt.continuousAt.tendsto.comp hg))
    (fun n ↦ abs_covariationSum_le (π n) f g)

end StochLean
