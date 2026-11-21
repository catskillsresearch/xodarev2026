/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.Semimartingale.StochasticArea.Covariation
public import StochLean.ForMathlib.Analysis.LevyAreaRiccati
public import StochLean.Probability.Process.Semimartingale.Complex.Preservation
public import StochLean.Probability.Process.Semimartingale.Ito.Preservation

/-! # The actual Riccati-compensated area exponential

The clock is explicit: it may be deterministic time or the existing continuous
bracket. The process is constructed from the actual area integral, and its
semimartingale, continuity, endpoint and norm properties are proved here.
The local-martingale property still requires the stochastic drift calculation.
-/

@[expose] public section

open MeasureTheory Filter StochLean
open scoped NNReal

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsFiniteMeasure P]
  {F : Filtration ℝ≥0 mΩ} {X Y Q : ℝ≥0 → Ω → ℝ}

noncomputable def IsSemimartingale.stochasticAreaExponent
    (hX : IsSemimartingale X F P) (hY : IsSemimartingale Y F P) (hF : F.IsUsual P)
    (Q : ℝ≥0 → Ω → ℝ) (u T : ℝ) : ℝ≥0 → Ω → ℂ :=
  complexProcess
    (fun t ω ↦ -(1 / 2 : ℝ) * (levyAreaAlpha u T (Q t ω) *
      (X t ω ^ 2 + Y t ω ^ 2)) + levyAreaBeta u T (Q t ω))
    (fun t ω ↦ u * hX.stochasticArea hY hF t ω)

noncomputable def IsSemimartingale.stochasticAreaExponential
    (hX : IsSemimartingale X F P) (hY : IsSemimartingale Y F P) (hF : F.IsUsual P)
    (Q : ℝ≥0 → Ω → ℝ) (u T : ℝ) : ℝ≥0 → Ω → ℂ :=
  fun t ω ↦ Complex.exp (hX.stochasticAreaExponent hY hF Q u T t ω)

theorem IsSemimartingale.stochasticAreaExponent_eq
    (hX : IsSemimartingale X F P) (hY : IsSemimartingale Y F P) (hF : F.IsUsual P)
    (Q : ℝ≥0 → Ω → ℝ) (u T : ℝ) (t : ℝ≥0) (ω : Ω) :
    hX.stochasticAreaExponent hY hF Q u T t ω =
      Complex.I * (u : ℂ) * (hX.stochasticArea hY hF t ω : ℂ) -
      (levyAreaAlpha u T (Q t ω) : ℂ) / 2 * ((X t ω : ℂ) ^ 2 + (Y t ω : ℂ) ^ 2) +
        (levyAreaBeta u T (Q t ω) : ℂ) := by
  apply Complex.ext
  · simp [stochasticAreaExponent, complexProcess, ← Complex.ofReal_pow]
    ring
  · simp [stochasticAreaExponent, complexProcess, ← Complex.ofReal_pow]

theorem IsSemimartingale.isComplexSemimartingale_stochasticAreaExponent
    (hX : IsSemimartingale X F P) (hY : IsSemimartingale Y F P)
    (hQ : IsSemimartingale Q F P) (hF : F.IsUsual P) (u T : ℝ) :
    IsComplexSemimartingale (hX.stochasticAreaExponent hY hF Q u T) F P := by
  have hα := hQ.contDiff_comp hF (contDiff_levyAreaAlpha u T)
  have hβ := hQ.contDiff_comp hF (contDiff_levyAreaBeta u T)
  have hR := (hX.contDiff_comp hF (show ContDiff ℝ 2 (fun x : ℝ ↦ x ^ 2) by fun_prop)).add
    (hY.contDiff_comp hF (show ContDiff ℝ 2 (fun x : ℝ ↦ x ^ 2) by fun_prop))
  exact (((hα.mul hR hF).const_mul (-(1 / 2 : ℝ))).add hβ).complex
    ((hX.isSemimartingale_stochasticArea hY hF).const_mul u)

theorem IsSemimartingale.isComplexSemimartingale_stochasticAreaExponential
    (hX : IsSemimartingale X F P) (hY : IsSemimartingale Y F P)
    (hQ : IsSemimartingale Q F P) (hF : F.IsUsual P) (u T : ℝ) :
    IsComplexSemimartingale (hX.stochasticAreaExponential hY hF Q u T) F P :=
  (hX.isComplexSemimartingale_stochasticAreaExponent hY hQ hF u T).differentiable_comp
    hF Complex.differentiable_exp

theorem IsSemimartingale.hasContinuousPaths_stochasticAreaExponent
    (hX : IsSemimartingale X F P) (hY : IsSemimartingale Y F P) (hF : F.IsUsual P)
    (hcX : HasContinuousPaths X P) (hcY : HasContinuousPaths Y P)
    (hcQ : HasContinuousPaths Q P) (u T : ℝ) :
    HasContinuousPaths (hX.stochasticAreaExponent hY hF Q u T) P := by
  filter_upwards [hcX, hcY, hcQ, hX.hasContinuousPaths_stochasticArea hY hF hcX hcY]
    with ω hx hy hq ha
  have hα := (contDiff_levyAreaAlpha u T (n := 2)).continuous.comp hq
  have hβ := (contDiff_levyAreaBeta u T (n := 2)).continuous.comp hq
  have hr : Continuous (fun t ↦ -(1 / 2 : ℝ) *
      (levyAreaAlpha u T (Q t ω) * (X t ω ^ 2 + Y t ω ^ 2)) +
        levyAreaBeta u T (Q t ω)) :=
    (continuous_const.mul (hα.mul ((hx.pow 2).add (hy.pow 2)))).add hβ
  have hi : Continuous (fun t ↦ u * hX.stochasticArea hY hF t ω) := continuous_const.mul ha
  apply ((Complex.continuous_ofReal.comp hr).add
    ((continuous_const : Continuous (fun _ : ℝ≥0 ↦ Complex.I)).mul
      (Complex.continuous_ofReal.comp hi))).congr
  intro t
  apply Complex.ext <;> simp [stochasticAreaExponent, complexProcess, -Complex.ofReal_pow]

theorem IsSemimartingale.hasContinuousPaths_stochasticAreaExponential
    (hX : IsSemimartingale X F P) (hY : IsSemimartingale Y F P) (hF : F.IsUsual P)
    (hcX : HasContinuousPaths X P) (hcY : HasContinuousPaths Y P)
    (hcQ : HasContinuousPaths Q P) (u T : ℝ) :
    HasContinuousPaths (hX.stochasticAreaExponential hY hF Q u T) P :=
  (hX.hasContinuousPaths_stochasticAreaExponent hY hF hcX hcY hcQ u T).mono
    (fun _ h ↦ Complex.continuous_exp.comp h)

theorem IsSemimartingale.norm_stochasticAreaExponential_le_one
    (hX : IsSemimartingale X F P) (hY : IsSemimartingale Y F P) (hF : F.IsUsual P)
    (u T : ℝ) (t : ℝ≥0) (ω : Ω) (hqt : Q t ω ≤ T) :
    ‖hX.stochasticAreaExponential hY hF Q u T t ω‖ ≤ 1 := by
  rw [stochasticAreaExponential, hX.stochasticAreaExponent_eq hY hF]
  exact norm_exp_levyAreaExponent_le_one u _ _ _ hqt

theorem IsSemimartingale.stochasticAreaExponential_at_terminal_level
    (hX : IsSemimartingale X F P) (hY : IsSemimartingale Y F P) (hF : F.IsUsual P)
    (u T : ℝ) (t : ℝ≥0) (ω : Ω) (hqt : Q t ω = T) :
    hX.stochasticAreaExponential hY hF Q u T t ω =
      Complex.exp (Complex.I * (u : ℂ) * (hX.stochasticArea hY hF t ω : ℂ)) := by
  rw [stochasticAreaExponential, hX.stochasticAreaExponent_eq hY hF, hqt]
  simp only [levyAreaAlpha_terminal, levyAreaBeta_terminal, Complex.ofReal_zero,
    zero_div, zero_mul, sub_zero, add_zero]

theorem IsSemimartingale.stochasticAreaExponential_zero_ae
    (hX : IsSemimartingale X F P) (hY : IsSemimartingale Y F P) (hF : F.IsUsual P)
    (hX0 : X 0 =ᵐ[P] 0) (hY0 : Y 0 =ᵐ[P] 0) (hQ0 : Q 0 =ᵐ[P] 0) (u T : ℝ) :
    hX.stochasticAreaExponential hY hF Q u T 0 =ᵐ[P]
      fun _ ↦ ((Real.cosh (u * T))⁻¹ : ℂ) := by
  filter_upwards [hX0, hY0, hQ0, hX.stochasticArea_zero_ae hY hF]
    with ω hx hy hq ha
  rw [stochasticAreaExponential, hX.stochasticAreaExponent_eq hY hF, hx, hy, hq, ha]
  simp only [Pi.zero_apply, Complex.ofReal_zero, zero_pow (by decide : 2 ≠ 0),
    mul_zero, zero_add, sub_zero, ← Complex.ofReal_exp, exp_levyAreaBeta, Complex.ofReal_inv]

end ProbabilityTheory
