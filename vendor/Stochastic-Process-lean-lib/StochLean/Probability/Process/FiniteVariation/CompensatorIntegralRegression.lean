/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.FiniteVariation.RightValueCompensator
public import StochLean.Probability.Process.FiniteVariation.StieltjesKernelVariation
public import StochLean.Probability.Process.Semimartingale.StochasticIntegral.ConstantIntegrator
public import StochLean.Probability.Process.Semimartingale.QuadraticCovariation.Constants

/-! # Initial-value regressions for the corrected compensator integral formulas

The constant-one source has zero actual variation kernel and an integrable
initial value. Nevertheless, its actual integral against a time-constant
initial-measurable integrand retains that integrand's arbitrary random initial
value. Only the centered integral is necessarily integrable.

For the right-value formula, the constant-one martingale and an arbitrary
initial-measurable constant FV source have left-value integral zero and raw
covariation equal to the source. The actual canonical compensator of their
sum is zero by the proved right-value compensator theorem. Neither regression
assumes a moment of the random constant or supplies a compensator candidate.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal

namespace StochLean.SemimartingaleRegression

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
  {F : Filtration ℝ≥0 mΩ} {Z : Ω → ℝ}

/-- Zero expected absolute increment integral does not control the original
initial product, even when the source's own initial value is integrable. -/
theorem stochasticIntegral_constant_one_initial_moment
    (hF : F.IsUsual P) (hZ : Measurable[F 0] Z) :
    let X : ℝ≥0 → Ω → ℝ := fun _ _ ↦ 1
    let H : ℝ≥0 → Ω → ℝ := fun _ ↦ Z
    let hX := isSemimartingale_const_initial (F := F) (P := P)
      (measurable_const (a := (1 : ℝ)))
    let haH : Adapted F H := fun _ ↦ hZ.mono (F.mono bot_le) le_rfl
    let hrH : HasCagladPaths H P := Eventually.of_forall fun _ ↦
      IsContinuousPath.isCagladPath continuous_const
    let κ := totalVariationKernel X hX.adapted
      (fun _ ↦ (monotone_const.monotoneOn univ).locallyBoundedVariationOn)
      (fun _ _ ↦ continuousWithinAt_const)
    let I := hX.stochasticIntegral hF haH hrH
    Integrable (X 0) P ∧ κ = 0 ∧ Indistinguishable I H P ∧
      Indistinguishable (fun t ω ↦ I t ω - Z ω) 0 P ∧
      ∀ T : ℝ≥0,
        (∫⁻ ω, ∫⁻ t in Ioc 0 T, ENNReal.ofReal ‖H t ω‖ ∂κ ω ∂P) = 0 ∧
        Integrable (fun ω ↦ I T ω - Z ω) P ∧
        (¬ Integrable Z P → ¬ Integrable (I T) P) := by
  intro X H hX haH hrH κ I
  have heI : Indistinguishable I H P := by
    filter_upwards [stochasticIntegral_const_initial
      (Z := fun _ : Ω ↦ (1 : ℝ)) measurable_const hF haH hrH] with ω hω t
    simpa only [mul_one] using hω t
  have he0 : Indistinguishable (fun t ω ↦ I t ω - Z ω) 0 P := by
    filter_upwards [heI] with ω hω t
    change I t ω - Z ω = 0
    rw [hω t]
    exact sub_self _
  have hκ : κ = 0 := by
    ext1 ω
    apply Measure.measure_univ_eq_zero.mp
    calc
      κ ω univ = eVariationOn (fun _ : ℝ≥0 ↦ (1 : ℝ)) univ :=
        totalVariationKernel_univ hX.adapted
          (fun _ ↦ (monotone_const.monotoneOn univ).locallyBoundedVariationOn)
          (fun _ _ ↦ continuousWithinAt_const) ω
      _ = 0 := by
        apply (eVariationOn.eq_zero_iff _).mpr
        intro s _ t _
        exact edist_self (1 : ℝ)
  refine ⟨integrable_const (1 : ℝ), hκ, heI, he0, fun T ↦ ?_⟩
  refine ⟨by simp only [hκ, zero_apply, Measure.restrict_zero, lintegral_zero_measure,
    lintegral_zero], ?_, ?_⟩
  · exact (integrable_zero _ _ _).congr (he0.ae_eq T).symm
  · intro hn hi
    exact hn (hi.congr (heI.ae_eq T))

/-- The actual right-value compensator formula retains the raw initial
product: `J = 0`, `J + [1,A] = A`, and its selected compensator is zero. -/
theorem rightValueIntegral_arbitrary_initial_constant
    (hF : F.IsUsual P) (hZ : Measurable[F 0] Z) :
    let M : ℝ≥0 → Ω → ℝ := fun _ _ ↦ 1
    let hM : IsLocalMartingale M F P :=
      (isContinuousLocalMartingale_const_initial (F := F) (P := P)
        (measurable_const (a := (1 : ℝ)))).1
    let hA := isSemimartingale_const_initial (P := P) hZ
    let haL := hM.1.leftLimitProcess_of_usual hF hM.2.1
    let hrL := hM.2.1.hasCagladPaths_leftLimitProcess
    let J := hA.stochasticIntegral hF haL hrL
    let R := J + (hM.isSemimartingale hF).quadraticCovariation hA hF
    ∃ hvR : HasLocallyIntegrableVariation R F P,
      Indistinguishable J 0 P ∧
      Indistinguishable R (fun _ ↦ Z) P ∧
      Indistinguishable
        (hvR.predictableCompensator
          ((hA.adapted_stochasticIntegral hF haL hrL).add
            ((hM.isSemimartingale hF).adapted_quadraticCovariation hA hF)) hF
          ((hA.hasCadlagPaths_stochasticIntegral hF haL hrL).add
            ((hM.isSemimartingale hF).hasCadlagPaths_quadraticCovariation hA hF)))
        0 P := by
  intro M hM hA haL hrL J R
  have hpA : IsStronglyPredictable F (fun _ : ℝ≥0 ↦ Z) :=
    hA.adapted.isStronglyPredictable_of_leftContinuous
      (fun _ _ ↦ continuousWithinAt_const)
  have hvA : HasFiniteVariationPaths (fun _ : ℝ≥0 ↦ Z) P :=
    (hasIntegrableVariation_const Z).hasFiniteVariationPaths
  have hvR : HasLocallyIntegrableVariation R F P :=
    hM.hasLocallyIntegrableVariation_rightValueIntegral hpA hF hA.hasCadlagPaths hvA
  have heJ : Indistinguishable J 0 P :=
    stochasticIntegral_const_initial_of_zero_initial_integrand hZ hF haL hrL
      (Eventually.of_forall fun ω ↦ by simp only [leftLimitProcess_zero, Pi.zero_apply])
  have heQ : Indistinguishable
      ((hM.isSemimartingale hF).quadraticCovariation hA hF) (fun _ ↦ Z) P := by
    filter_upwards [hA.quadraticCovariation_const_initial_left
      (Z := fun _ : Ω ↦ (1 : ℝ)) measurable_const hF] with ω hω t
    simpa only [one_mul] using hω t
  have heR : Indistinguishable R (fun _ ↦ Z) P := by
    filter_upwards [heJ, heQ] with ω hj hq t
    change J t ω + (hM.isSemimartingale hF).quadraticCovariation hA hF t ω = Z ω
    rw [hj t, hq t]
    exact zero_add _
  refine ⟨hvR, heJ, heR, ?_⟩
  exact (hM.predictableCompensator_rightValueIntegral hpA hF hA.hasCadlagPaths hvA).trans heJ

end StochLean.SemimartingaleRegression
