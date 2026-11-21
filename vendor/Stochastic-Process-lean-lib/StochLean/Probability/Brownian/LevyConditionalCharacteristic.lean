/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import
  StochLean.Probability.Process.Semimartingale.StochasticExponential.CharacteristicMartingale
public import StochLean.ForMathlib.MeasureTheory.ConditionalComplexMultiplication

/-! # The conditional characteristic function in Levy's characterization

The compensated exponential martingale and the bounded past phase give
the actual conditional characteristic function of every future increment.
No Gaussian law or increment independence is assumed.
-/

@[expose] public section

open MeasureTheory StochLean
open scoped NNReal

namespace ProbabilityTheory

theorem IsContinuousLocalMartingale.condExp_characteristic_increment
    {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsFiniteMeasure P]
    {F : Filtration ℝ≥0 mΩ} {X : ℝ≥0 → Ω → ℝ}
    (hM : IsContinuousLocalMartingale X F P) (hF : F.IsUsual P)
    (hq : Indistinguishable ((hM.isSemimartingale hF).continuousQuadraticVariation hF)
      (fun t _ ↦ (t : ℝ)) P) {s t : ℝ≥0} (hst : s ≤ t) (u : ℝ) :
    P[fun ω ↦ Complex.exp (Complex.I * (u : ℂ) * ((X t ω - X s ω : ℝ) : ℂ)) | F s] =ᵐ[P]
      fun _ ↦ Complex.exp (Complex.ofReal (-((1 / 2 : ℝ) * u ^ 2) * ((t : ℝ) - (s : ℝ)))) := by
  let hX := hM.isSemimartingale hF
  let E := hX.characteristicExponential hF u
  let a := fun r : ℝ≥0 ↦ ((1 / 2 : ℝ) * u ^ 2) * r
  let f : Ω → ℂ := fun ω ↦ Complex.exp
    (-Complex.ofReal (a t) - (Complex.I * (u : ℂ)) * Complex.ofReal (X s ω))
  have hf : Measurable[F s] f := Complex.continuous_exp.measurable.comp
    (measurable_const.sub ((Complex.continuous_ofReal.measurable.comp (hX.adapted s)).const_mul
      (Complex.I * (u : ℂ))))
  have hfn (ω : Ω) : ‖f ω‖ = Real.exp (-a t) := by
    simp [f, Complex.norm_exp]
  have hEm := hM.martingale_characteristicExponential_of_bracket_eq_time hF hq u
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
      (fun _ ↦ Complex.exp (Complex.ofReal (-((1 / 2 : ℝ) * u ^ 2) *
        ((t : ℝ) - (s : ℝ))))) := by
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
