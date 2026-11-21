/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Martingale.DiscreteIntegral
public import StochLean.Probability.Martingale.QuadraticVariation

/-! # L2 isometry and estimates for discrete predictable integrals

These estimates will be reused on sampled stopping-time partitions. The integral and discrete
bracket are the existing canonical owners; no continuous-time bracket is introduced here.
-/

@[expose] public section

open Filter Finset
open scoped NNReal ENNReal BigOperators

namespace MeasureTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
  {F : Filtration ℕ mΩ} {M H : ℕ → Ω → ℝ}

theorem memLp_discreteStochasticIntegral
    (hM : ∀ n, MemLp (M n) 2 P) (hH : IsStronglyPredictable F H)
    (hb : ∀ n, ∃ C : ℝ, ∀ᵐ ω ∂P, ‖H n ω‖ ≤ C) (n : ℕ) :
    MemLp (discreteStochasticIntegral H M n) 2 P := by
  rw [discreteStochasticIntegral_eq_sum]
  apply memLp_finsetSum'
  intro k _
  obtain ⟨C, hC⟩ := hb (k + 1)
  exact ((hM (k + 1)).sub (hM k)).smul
    (memLp_top_of_bound ((hH.measurable_add_one k).mono (F.le k)).aestronglyMeasurable C hC)

/-- The elementary algebraic identity behind the isometry is pointwise, independent of any
martingale assumption. -/
theorem pathwiseQuadraticVariation_discreteStochasticIntegral (H M : ℕ → Ω → ℝ) (n : ℕ) :
    pathwiseQuadraticVariation (discreteStochasticIntegral H M) n = fun ω ↦
      ∑ k ∈ range n, (H (k + 1) ω) ^ 2 * (M (k + 1) ω - M k ω) ^ 2 := by
  funext ω
  apply sum_congr rfl
  intro k _
  have heq := congrFun (discreteStochasticIntegral_succ H M k) ω
  simp only [Pi.add_apply, smul_eq_mul, Pi.mul_apply, Pi.sub_apply] at heq
  rw [heq]
  ring

variable [IsFiniteMeasure P] [SigmaFiniteFiltration P F]

theorem Martingale.integral_pathwiseQuadraticVariation_eq_integral_sub_initial_sq
    (hM : Martingale M F P) (hlp : ∀ n, MemLp (M n) 2 P) (n : ℕ) :
    ∫ ω, pathwiseQuadraticVariation M n ω ∂P = ∫ ω, (M n ω - M 0 ω) ^ 2 ∂P :=
  (integral_pathwiseQuadraticVariation_eq_predictableQuadraticVariation hM.stronglyAdapted
    (fun k ↦ ((hlp (k + 1)).sub (hlp k)).integrable_sq) n).trans
      (hM.integral_sub_initial_sq_eq_integral_predictableQuadraticVariation hlp n).symm

/-- The discrete Ito isometry with sectionwise essential bounds on the predictable integrand. -/
theorem Martingale.integral_sq_discreteStochasticIntegral
    (hM : Martingale M F P) (hlp : ∀ n, MemLp (M n) 2 P)
    (hH : IsStronglyPredictable F H) (hb : ∀ n, ∃ C : ℝ, ∀ᵐ ω ∂P, ‖H n ω‖ ≤ C)
    (n : ℕ) :
    ∫ ω, (MeasureTheory.discreteStochasticIntegral H M n ω) ^ 2 ∂P =
      ∫ ω, ∑ k ∈ range n, (H (k + 1) ω) ^ 2 * (M (k + 1) ω - M k ω) ^ 2 ∂P := by
  have hI := hM.discreteStochasticIntegral hH hb
  have hIlp := memLp_discreteStochasticIntegral hlp hH hb
  have h := hI.integral_pathwiseQuadraticVariation_eq_integral_sub_initial_sq hIlp n
  simpa only [pathwiseQuadraticVariation_discreteStochasticIntegral,
    MeasureTheory.discreteStochasticIntegral_zero, Pi.zero_apply, sub_zero] using h.symm

/-- A common coefficient bound gives a deterministic L2 energy estimate. -/
theorem Martingale.integral_sq_discreteStochasticIntegral_le
    (hM : Martingale M F P) (hlp : ∀ n, MemLp (M n) 2 P)
    (hH : IsStronglyPredictable F H) (C : ℝ≥0)
    (hb : ∀ n, ∀ᵐ ω ∂P, ‖H n ω‖ ≤ C) (n : ℕ) :
    ∫ ω, (MeasureTheory.discreteStochasticIntegral H M n ω) ^ 2 ∂P ≤
      (C : ℝ) ^ 2 * ∫ ω, (M n ω - M 0 ω) ^ 2 ∂P := by
  have hIb : ∀ k, ∃ R : ℝ, ∀ᵐ ω ∂P, ‖H k ω‖ ≤ R := fun k ↦ ⟨(C : ℝ), hb k⟩
  have hIlp := memLp_discreteStochasticIntegral hlp hH hIb
  have hi : Integrable (pathwiseQuadraticVariation M n) P :=
    integrable_pathwiseQuadraticVariation (fun k ↦ ((hlp (k + 1)).sub (hlp k)).integrable_sq) n
  have hIhi : Integrable
      (pathwiseQuadraticVariation (MeasureTheory.discreteStochasticIntegral H M) n) P :=
    integrable_pathwiseQuadraticVariation
      (fun k ↦ ((hIlp (k + 1)).sub (hIlp k)).integrable_sq) n
  have hpoint : ∀ᵐ ω ∂P,
      pathwiseQuadraticVariation (MeasureTheory.discreteStochasticIntegral H M) n ω ≤
        (C : ℝ) ^ 2 * pathwiseQuadraticVariation M n ω := by
    filter_upwards [ae_all_iff.mpr hb] with ω hω
    rw [pathwiseQuadraticVariation_discreteStochasticIntegral, pathwiseQuadraticVariation, mul_sum]
    apply sum_le_sum
    intro k _
    apply mul_le_mul_of_nonneg_right ?_ (sq_nonneg _)
    rw [← sq_abs (H (k + 1) ω)]
    exact pow_le_pow_left₀ (abs_nonneg _) (by simpa only [Real.norm_eq_abs] using hω (k + 1)) 2
  calc
    _ = ∫ ω, pathwiseQuadraticVariation (MeasureTheory.discreteStochasticIntegral H M) n ω ∂P := by
      have hIm := hM.discreteStochasticIntegral hH hIb
      simpa only [MeasureTheory.discreteStochasticIntegral_zero, Pi.zero_apply, sub_zero] using
        (hIm.integral_pathwiseQuadraticVariation_eq_integral_sub_initial_sq hIlp n).symm
    _ ≤ ∫ ω, (C : ℝ) ^ 2 * pathwiseQuadraticVariation M n ω ∂P :=
      integral_mono_ae hIhi (hi.const_mul _) hpoint
    _ = (C : ℝ) ^ 2 * ∫ ω, (M n ω - M 0 ω) ^ 2 ∂P := by
      rw [integral_const_mul,
        hM.integral_pathwiseQuadraticVariation_eq_integral_sub_initial_sq hlp n]

end MeasureTheory
