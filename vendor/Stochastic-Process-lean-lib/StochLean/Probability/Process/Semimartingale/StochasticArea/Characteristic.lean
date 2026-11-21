/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.Semimartingale.StochasticArea.ExponentialMartingale
public import StochLean.Probability.Process.LocalMartingale.ComplexStopping
public import StochLean.Probability.Process.LocalMartingale.ComplexBounded

/-! # Levy's stochastic-area characteristic function at a deterministic clock level

The actual compensated exponential stopped at a deterministic time is bounded
by one when the common raw clock has a deterministic terminal level. Its proved
local-martingale property therefore gives a true complex martingale. Comparing
its actual endpoints proves the inverse-cosh characteristic function.
-/

@[expose] public section

open MeasureTheory Filter Set
open scoped NNReal

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
  {F : Filtration ℝ≥0 mΩ} {X Y Q : ℝ≥0 → Ω → ℝ}

theorem IsContinuousLocalMartingale.martingale_stopped_stochasticAreaExponential
    [IsFiniteMeasure P] [SigmaFiniteFiltration P F]
    (hX : IsContinuousLocalMartingale X F P) (hY : IsContinuousLocalMartingale Y F P)
    (hQ : IsSemimartingale Q F P) (hF : F.IsUsual P)
    (hqX : Indistinguishable ((hX.isSemimartingale hF).quadraticVariation hF) Q P)
    (hqY : Indistinguishable ((hY.isSemimartingale hF).quadraticVariation hF) Q P)
    (ho : Indistinguishable
      ((hX.isSemimartingale hF).continuousQuadraticCovariation (hY.isSemimartingale hF) hF) 0 P)
    (hvQ : HasFiniteVariationPaths Q P) (hcQ : HasContinuousPaths Q P)
    (h0X : X 0 =ᵐ[P] 0) (h0Y : Y 0 =ᵐ[P] 0) (h0Q : Q 0 =ᵐ[P] 0)
    (u T : ℝ) (S : ℝ≥0) (hQS : Q S =ᵐ[P] fun _ ↦ T) :
    Martingale (MeasureTheory.stoppedProcess
      ((hX.isSemimartingale hF).stochasticAreaExponential (hY.isSemimartingale hF) hF Q u T)
      (fun _ : Ω ↦ (S : WithTop ℝ≥0))) F P := by
  let hSX := hX.isSemimartingale hF
  let hSY := hY.isSemimartingale hF
  have hL := hX.isComplexLocalMartingale_stochasticAreaExponential hY hQ hF hqX hqY ho
    hvQ hcQ h0X h0Y h0Q u T
  apply (hL.stoppedProcess hF (isStoppingTime_const F S)).martingale_of_integrable_envelope
  intro _
  refine ⟨fun _ : Ω ↦ (1 : ℝ), integrable_const 1, ?_⟩
  filter_upwards [hSX.hasMonotonePaths_quadraticVariation hF, hqX, hQS]
    with ω hm hq hterm t _ht
  by_cases ht : t ≤ S
  · rw [MeasureTheory.stoppedProcess_eq_of_le
      (τ := fun _ : Ω ↦ (S : WithTop ℝ≥0)) (ω := ω) (WithTop.coe_le_coe.mpr ht)]
    apply hSX.norm_stochasticAreaExponential_le_one hSY hF u T t ω
    calc
      Q t ω = hSX.quadraticVariation hF t ω := (hq t).symm
      _ ≤ hSX.quadraticVariation hF S ω := hm ht
      _ = Q S ω := hq S
      _ = T := hterm
  · rw [MeasureTheory.stoppedProcess_eq_of_ge
      (τ := fun _ : Ω ↦ (S : WithTop ℝ≥0)) (ω := ω)
      (WithTop.coe_le_coe.mpr (le_of_not_ge ht))]
    apply hSX.norm_stochasticAreaExponential_le_one hSY hF u T S ω
    exact le_of_eq hterm

theorem IsContinuousLocalMartingale.integral_exp_stochasticArea_eq_inv_cosh
    [IsProbabilityMeasure P] [SigmaFiniteFiltration P F]
    (hX : IsContinuousLocalMartingale X F P) (hY : IsContinuousLocalMartingale Y F P)
    (hQ : IsSemimartingale Q F P) (hF : F.IsUsual P)
    (hqX : Indistinguishable ((hX.isSemimartingale hF).quadraticVariation hF) Q P)
    (hqY : Indistinguishable ((hY.isSemimartingale hF).quadraticVariation hF) Q P)
    (ho : Indistinguishable
      ((hX.isSemimartingale hF).continuousQuadraticCovariation (hY.isSemimartingale hF) hF) 0 P)
    (hvQ : HasFiniteVariationPaths Q P) (hcQ : HasContinuousPaths Q P)
    (h0X : X 0 =ᵐ[P] 0) (h0Y : Y 0 =ᵐ[P] 0) (h0Q : Q 0 =ᵐ[P] 0)
    (u T : ℝ) (S : ℝ≥0) (hQS : Q S =ᵐ[P] fun _ ↦ T) :
    (∫ ω, Complex.exp (Complex.I * (u : ℂ) *
      ((hX.isSemimartingale hF).stochasticArea (hY.isSemimartingale hF) hF S ω : ℂ)) ∂P) =
        ((Real.cosh (u * T))⁻¹ : ℂ) := by
  let hSX := hX.isSemimartingale hF
  let hSY := hY.isSemimartingale hF
  let E := hSX.stochasticAreaExponential hSY hF Q u T
  have hM := hX.martingale_stopped_stochasticAreaExponential hY hQ hF hqX hqY ho
    hvQ hcQ h0X h0Y h0Q u T S hQS
  change Martingale (MeasureTheory.stoppedProcess E (fun _ : Ω ↦ (S : WithTop ℝ≥0))) F P at hM
  have he0 : MeasureTheory.stoppedProcess E (fun _ : Ω ↦ (S : WithTop ℝ≥0)) 0 = E 0 := by
    funext ω
    exact MeasureTheory.stoppedProcess_eq_of_le
      (WithTop.coe_le_coe.mpr (show (0 : ℝ≥0) ≤ S from bot_le))
  have heS : MeasureTheory.stoppedProcess E (fun _ : Ω ↦ (S : WithTop ℝ≥0)) S = E S := by
    funext ω
    exact MeasureTheory.stoppedProcess_eq_of_le le_rfl
  have hInt : (∫ ω, E 0 ω ∂P) = ∫ ω, E S ω ∂P := by
    have h := hM.setIntegral_eq (show (0 : ℝ≥0) ≤ S from bot_le)
      (s := univ) MeasurableSet.univ
    simpa only [Measure.restrict_univ, he0, heS] using h
  have hterm : E S =ᵐ[P] fun ω ↦ Complex.exp (Complex.I * (u : ℂ) *
      (hSX.stochasticArea hSY hF S ω : ℂ)) := by
    filter_upwards [hQS] with ω hq
    exact hSX.stochasticAreaExponential_at_terminal_level hSY hF u T S ω hq
  calc
    _ = ∫ ω, E S ω ∂P := integral_congr_ae hterm.symm
    _ = ∫ ω, E 0 ω ∂P := hInt.symm
    _ = ∫ _ω : Ω, ((Real.cosh (u * T))⁻¹ : ℂ) ∂P := integral_congr_ae
      (hSX.stochasticAreaExponential_zero_ae hSY hF h0X h0Y h0Q u T)
    _ = _ := by simp

end ProbabilityTheory
