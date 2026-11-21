/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.Semimartingale.Complex.LeftLimitIntegral
public import StochLean.Probability.Process.Semimartingale.Complex.BracketIntegral
public import
  StochLean.Probability.Process.Semimartingale.QuadraticCovariation.ContinuousPartAlgebra

/-! # Combining the four ordered analytic Hessian integrals

Both off-diagonal entries are included. The second imaginary derivative
has the negative sign required by the bilinear, not Hermitian, bracket.
-/

@[expose] public section

open MeasureTheory
open scoped NNReal

namespace ProbabilityTheory

theorem stochasticIntegral_complex_left_hessian
    {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsFiniteMeasure P]
    {F : Filtration ℝ≥0 mΩ} {X : Fin 2 → ℝ≥0 → Ω → ℝ}
    {E : Fin 2 → Fin 2 → ℝ≥0 → Ω → ℝ} {G : ℝ≥0 → Ω → ℂ}
    (hX : ∀ i, IsSemimartingale (X i) F P) (hF : F.IsUsual P)
    (ha : Adapted F G) (hr : HasCadlagPaths G P) (L : ℂ →L[ℝ] ℝ)
    (haE : ∀ i j, Adapted F (E i j)) (hrE : ∀ i j, HasCadlagPaths (E i j) P)
    (hE : ∀ i j t ω, E i j t ω =
      ![![L (G t ω), L (Complex.I * G t ω)],
        ![L (Complex.I * G t ω), -L (G t ω)]] i j) :
    Indistinguishable
      (fun t ω ↦ ∑ i, ∑ j,
        ((hX i).isSemimartingale_continuousQuadraticCovariation (hX j) hF).stochasticIntegral
          hF ((haE i j).leftLimitProcess_of_usual hF (hrE i j))
          (hrE i j).hasCagladPaths_leftLimitProcess t ω)
      (fun t ω ↦ L ((((hX 0).complex (hX 1)).isComplexSemimartingale_continuousQuadraticVariation
        hF).stochasticIntegral hF
          (Adapted.complexLeftLimitProcess_of_usual ha hF hr)
          hr.hasCagladPaths_complexLeftLimitProcess t ω)) P := by
  let LI : ℂ →L[ℝ] ℝ := L.comp (Complex.I • (1 : ℂ →L[ℝ] ℂ))
  let M : Fin 2 → Fin 2 → ℂ →L[ℝ] ℝ := ![![L, LI], ![LI, -L]]
  have he (i j : Fin 2) (t : ℝ≥0) (ω : Ω) : E i j t ω = M i j (G t ω) := by
    rw [hE]
    fin_cases i <;> fin_cases j <;> simp [M, LI, smul_eq_mul]
  let haC := Adapted.complexLeftLimitProcess_of_usual ha hF hr
  let hrC := hr.hasCagladPaths_complexLeftLimitProcess
  have hj := ae_all_iff.mpr (fun i ↦ ae_all_iff.mpr (fun j ↦
    IsSemimartingale.stochasticIntegral_complex_left_component_of_eq
      ((hX i).isSemimartingale_continuousQuadraticCovariation (hX j) hF) hF ha hr (M i j)
      (haE i j) (hrE i j) (he i j)))
  have h00 := IsSemimartingale.complexIntegrandIntegral_congr_integrator
    ((hX 0).isSemimartingale_continuousQuadraticCovariation (hX 0) hF)
    ((hX 0).isSemimartingale_continuousQuadraticVariation hF) hF haC hrC
    ((hX 0).continuousQuadraticCovariation_self hF)
  have h11 := IsSemimartingale.complexIntegrandIntegral_congr_integrator
    ((hX 1).isSemimartingale_continuousQuadraticCovariation (hX 1) hF)
    ((hX 1).isSemimartingale_continuousQuadraticVariation hF) hF haC hrC
    ((hX 1).continuousQuadraticCovariation_self hF)
  have h10 := IsSemimartingale.complexIntegrandIntegral_congr_integrator
    ((hX 1).isSemimartingale_continuousQuadraticCovariation (hX 0) hF)
    ((hX 0).isSemimartingale_continuousQuadraticCovariation (hX 1) hF) hF haC hrC
    ((hX 1).continuousQuadraticCovariation_comm (hX 0) hF)
  filter_upwards [hj, h00, h11, h10,
    ((hX 0).complex (hX 1)).stochasticIntegral_continuousQuadraticVariation_coordinates
      hF haC hrC] with ω hi hi00 hi11 hi10 hb t
  simp only [Fin.sum_univ_two, hi, M, Matrix.cons_val_zero, Matrix.cons_val_one,
    neg_apply]
  rw [hi00 t, hi11 t, hi10 t, hb t]
  have htwo (z : ℂ) : Complex.I * (2 * z) = (2 : ℝ) • (Complex.I * z) := by
    simp only [Complex.real_smul, Complex.ofReal_ofNat]
    ring
  simp only [complexProcess, htwo, map_add, map_sub, map_smul, smul_eq_mul, LI,
    ContinuousLinearMap.comp_apply, smul_apply, one_apply_eq_self]
  ring

end ProbabilityTheory
