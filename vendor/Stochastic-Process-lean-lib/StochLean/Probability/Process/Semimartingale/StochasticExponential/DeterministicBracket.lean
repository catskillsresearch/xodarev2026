/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import
  StochLean.Probability.Process.Semimartingale.StochasticExponential.CharacteristicMartingale
public import StochLean.ForMathlib.MeasureTheory.ConditionalComplexMultiplication

/-! # Characteristic martingales for deterministic continuous brackets

The deterministic clock need not be strictly increasing or linear. Compact
bounds follow from monotonicity of the existing continuous bracket on each
path, so no redundant monotonicity hypothesis on the clock is imposed.
-/

@[expose] public section

open MeasureTheory StochLean
open scoped NNReal

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsFiniteMeasure P]
  {F : Filtration ℝ≥0 mΩ} {X : ℝ≥0 → Ω → ℝ}

theorem IsContinuousLocalMartingale.martingale_characteristicExponential_of_deterministic_bracket
    (hM : IsContinuousLocalMartingale X F P) (hF : F.IsUsual P) {q : ℝ≥0 → ℝ}
    (hq : Indistinguishable ((hM.isSemimartingale hF).continuousQuadraticVariation hF)
      (fun t _ ↦ q t) P) (u : ℝ) :
    Martingale ((hM.isSemimartingale hF).characteristicExponential hF u) F P := by
  apply IsComplexLocalMartingale.martingale_of_integrable_envelope
    (hM.isComplexLocalMartingale_characteristicExponential hF u)
  intro T
  refine ⟨fun _ ↦ Real.exp (((1 / 2 : ℝ) * u ^ 2) * q T), integrable_const _, ?_⟩
  filter_upwards [hq.ae_eq T] with ω hqω t ht
  rw [IsSemimartingale.norm_characteristicExponential]
  apply Real.exp_le_exp.mpr
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  rw [← hqω]
  exact (hM.isSemimartingale hF).monotone_continuousQuadraticVariation hF ω ht

theorem IsContinuousLocalMartingale.condExp_characteristic_increment_of_deterministic_bracket
    (hM : IsContinuousLocalMartingale X F P) (hF : F.IsUsual P) {q : ℝ≥0 → ℝ}
    (hq : Indistinguishable ((hM.isSemimartingale hF).continuousQuadraticVariation hF)
      (fun t _ ↦ q t) P) {s t : ℝ≥0} (hst : s ≤ t) (u : ℝ) :
    P[fun ω ↦ Complex.exp (Complex.I * (u : ℂ) * ((X t ω - X s ω : ℝ) : ℂ)) | F s] =ᵐ[P]
      fun _ ↦ Complex.exp (Complex.ofReal (-((1 / 2 : ℝ) * u ^ 2) * (q t - q s))) := by
  let hX := hM.isSemimartingale hF
  let E := hX.characteristicExponential hF u
  let a := fun r : ℝ≥0 ↦ ((1 / 2 : ℝ) * u ^ 2) * q r
  let f : Ω → ℂ := fun ω ↦ Complex.exp
    (-Complex.ofReal (a t) - (Complex.I * (u : ℂ)) * Complex.ofReal (X s ω))
  have hf : Measurable[F s] f := Complex.continuous_exp.measurable.comp
    (measurable_const.sub ((Complex.continuous_ofReal.measurable.comp (hX.adapted s)).const_mul
      (Complex.I * (u : ℂ))))
  have hfn (ω : Ω) : ‖f ω‖ = Real.exp (-a t) := by simp [f, Complex.norm_exp]
  have hEm := hM.martingale_characteristicExponential_of_deterministic_bracket hF hq u
  have hpull := condExp_complex_mul_of_bound (F.le s) hf.stronglyMeasurable
    (hEm.integrable t) (Real.exp (-a t))
    (Filter.Eventually.of_forall (fun ω ↦ (hfn ω).le))
  have hprod : (fun ω ↦ f ω * E t ω) =ᵐ[P]
      (fun ω ↦ Complex.exp (Complex.I * (u : ℂ) * ((X t ω - X s ω : ℝ) : ℂ))) := by
    filter_upwards [hq.ae_eq t] with ω hqω
    change Complex.exp _ * Complex.exp (hX.characteristicExponent hF u t ω) = _
    rw [← Complex.exp_add]
    congr 1
    apply Complex.ext <;>
      simp [IsSemimartingale.characteristicExponent, complexProcess, hqω, a, pow_two]
    all_goals ring
  have hright : (fun ω ↦ f ω * E s ω) =ᵐ[P]
      (fun _ ↦ Complex.exp (Complex.ofReal (-((1 / 2 : ℝ) * u ^ 2) * (q t - q s)))) := by
    filter_upwards [hq.ae_eq s] with ω hqω
    change Complex.exp _ * Complex.exp (hX.characteristicExponent hF u s ω) = _
    rw [← Complex.exp_add]
    congr 1
    apply Complex.ext <;>
      simp [IsSemimartingale.characteristicExponent, complexProcess, hqω, a, pow_two]
    all_goals ring
  filter_upwards [condExp_congr_ae (m := F s) hprod, hpull,
    hEm.condExp_ae_eq hst, hright] with ω hprodω hpullω hEmω hrightω
  exact hprodω.symm.trans (hpullω.trans ((congrArg (f ω * ·) hEmω).trans hrightω))

end ProbabilityTheory
