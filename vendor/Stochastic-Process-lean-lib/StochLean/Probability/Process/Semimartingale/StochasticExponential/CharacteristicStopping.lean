/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import
  StochLean.Probability.Process.Semimartingale.StochasticExponential.CharacteristicMartingale
public import StochLean.Probability.Process.LocalMartingale.ComplexStopping
public import StochLean.Probability.Martingale.OptionalSampling.ComplexBounded
public import StochLean.Probability.Process.Stopping.LeftContinuousSampling
public import StochLean.ForMathlib.MeasureTheory.ConditionalComplexMultiplication

/-! # Conditional characteristic functions at bounded-bracket stopping times

The characteristic exponential stopped before a fixed bracket level is
uniformly bounded. Almost-surely finite optional sampling therefore computes
the conditional characteristic function of stopped increments without first
assuming moment identities, a Brownian law or a martingale time-change theorem.
-/

@[expose] public section

open MeasureTheory StochLean
open scoped NNReal

namespace ProbabilityTheory

theorem IsContinuousLocalMartingale.condExp_characteristic_at_stoppingTimes
    {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsFiniteMeasure P]
    {F : Filtration ℝ≥0 mΩ} {X : ℝ≥0 → Ω → ℝ}
    (hM : IsContinuousLocalMartingale X F P) (hF : F.IsUsual P)
    {σ τ : Ω → WithTop ℝ≥0} (hσ : IsStoppingTime F σ) (hτ : IsStoppingTime F τ)
    (hle : ∀ᵐ ω ∂P, σ ω ≤ τ ω) (hfinite : ∀ᵐ ω ∂P, τ ω ≠ ⊤) (q : ℝ≥0)
    (hb : ∀ᵐ ω ∂P, ∀ t, MeasureTheory.stoppedProcess
      ((hM.isSemimartingale hF).continuousQuadraticVariation hF) τ t ω ≤ q)
    (a b : ℝ)
    (hQa : stoppedValue ((hM.isSemimartingale hF).continuousQuadraticVariation hF) σ =ᵐ[P]
      fun _ ↦ a)
    (hQb : stoppedValue ((hM.isSemimartingale hF).continuousQuadraticVariation hF) τ =ᵐ[P]
      fun _ ↦ b) (u : ℝ) :
    P[fun ω ↦ Complex.exp (Complex.I * (u : ℂ) *
      ((stoppedValue X τ ω - stoppedValue X σ ω : ℝ) : ℂ)) | hσ.measurableSpace] =ᵐ[P]
        fun _ ↦ Complex.exp (Complex.ofReal (-((1 / 2 : ℝ) * u ^ 2) * (b - a))) := by
  let hX := hM.isSemimartingale hF
  let E := hX.characteristicExponential hF u
  let Z := MeasureTheory.stoppedProcess E τ
  let c : ℝ := (1 / 2) * u ^ 2
  let C : ℝ≥0 := ⟨Real.exp (c * q), (Real.exp_pos _).le⟩
  have hZ : IsComplexLocalMartingale Z F P :=
    (hM.isComplexLocalMartingale_characteristicExponential hF u).stoppedProcess hF hτ
  have hbound : ∀ᵐ ω ∂P, ∀ t, ‖Z t ω‖ ≤ C := by
    filter_upwards [hb] with ω hω t
    change ‖E (min (t : WithTop ℝ≥0) (τ ω)).untopA ω‖ ≤ Real.exp (c * q)
    rw [hX.norm_characteristicExponential hF u]
    exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (hω t) (by positivity))
  have hfσ : ∀ᵐ ω ∂P, σ ω ≠ ⊤ := by
    filter_upwards [hle, hfinite] with ω hleω hfω
    exact ne_top_of_le_ne_top hfω hleω
  have heτ : stoppedValue Z τ =ᵐ[P] stoppedValue E τ := by
    filter_upwards [stoppedValue_stoppedProcess_ae_eq (u := E) (τ := τ) hfinite] with ω h
    simpa only [min_self] using h
  have heσ : stoppedValue Z σ =ᵐ[P] stoppedValue E σ := by
    filter_upwards [hfσ, hle] with ω h ho
    change MeasureTheory.stoppedProcess E τ (σ ω).untopA ω = E (σ ω).untopA ω
    apply stoppedProcess_eq_of_le
    rw [WithTop.untopA_eq_untop h, WithTop.coe_untop]
    exact ho
  have hi := (hZ.integrable_stoppedValue_of_ae_finite_of_bound hF C hbound hτ hfinite).congr heτ
  have hCE : P[stoppedValue E τ | hσ.measurableSpace] =ᵐ[P] stoppedValue E σ :=
    (condExp_congr_ae heτ).symm.trans
      ((hZ.condExp_stoppedValue_of_ae_finite_of_bound hF C hbound hσ hτ hle hfinite).trans heσ)
  let f : Ω → ℂ := fun ω ↦ Complex.exp
    (-Complex.ofReal (c * b) - Complex.I * (u : ℂ) * Complex.ofReal (stoppedValue X σ ω))
  have hXS := hX.adapted.measurable_stoppedValue_of_leftContinuous_usual hF
    (hM.2.mono fun _ hω _ ↦ hω.continuousWithinAt) hσ
  have hf : Measurable[hσ.measurableSpace] f := Complex.continuous_exp.measurable.comp
    (measurable_const.sub ((Complex.continuous_ofReal.measurable.comp hXS).const_mul
      (Complex.I * (u : ℂ))))
  have hfn (ω : Ω) : ‖f ω‖ = Real.exp (-c * b) := by
    simp [f, Complex.norm_exp, neg_mul]
  have hpull := condExp_complex_mul_of_bound hσ.measurableSpace_le hf.stronglyMeasurable
    hi (Real.exp (-c * b)) (Filter.Eventually.of_forall (fun ω ↦ (hfn ω).le))
  have hprod : (fun ω ↦ f ω * stoppedValue E τ ω) =ᵐ[P]
      (fun ω ↦ Complex.exp (Complex.I * (u : ℂ) *
        ((stoppedValue X τ ω - stoppedValue X σ ω : ℝ) : ℂ))) := by
    filter_upwards [hQb] with ω hq
    change hX.continuousQuadraticVariation hF (τ ω).untopA ω = b at hq
    change Complex.exp _ * Complex.exp (hX.characteristicExponent hF u (τ ω).untopA ω) = _
    rw [← Complex.exp_add]
    congr 1
    apply Complex.ext <;> simp [IsSemimartingale.characteristicExponent, complexProcess,
      stoppedValue, hq, c, pow_two]
    all_goals ring
  have hright : (fun ω ↦ f ω * stoppedValue E σ ω) =ᵐ[P]
      (fun _ ↦ Complex.exp (Complex.ofReal (-((1 / 2 : ℝ) * u ^ 2) * (b - a)))) := by
    filter_upwards [hQa] with ω hq
    change hX.continuousQuadraticVariation hF (σ ω).untopA ω = a at hq
    change Complex.exp _ * Complex.exp (hX.characteristicExponent hF u (σ ω).untopA ω) = _
    rw [← Complex.exp_add]
    congr 1
    apply Complex.ext <;> simp [IsSemimartingale.characteristicExponent, complexProcess,
      stoppedValue, hq, c, pow_two]
    all_goals ring
  filter_upwards [condExp_congr_ae (m := hσ.measurableSpace) hprod, hpull, hCE, hright]
    with ω hp hh he hr
  exact hp.symm.trans (hh.trans ((congrArg (f ω * ·) he).trans hr))

end ProbabilityTheory
