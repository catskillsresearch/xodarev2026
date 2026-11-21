/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import
  StochLean.Probability.Process.Semimartingale.StochasticExponential.CharacteristicEquation
public import StochLean.Probability.Process.Semimartingale.Complex.LocalL2
public import StochLean.Probability.Process.Semimartingale.LocalL2Martingale
public import StochLean.Probability.Process.LocalMartingale.ComplexBounded

/-! # The characteristic exponential is a local martingale

When the continuous bracket is time, its norm has a deterministic bound on
every compact horizon, so it is a genuine complex martingale. No initial
moment condition is needed, and zero initial value is not silently imposed.
-/

@[expose] public section

open MeasureTheory
open scoped NNReal

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsFiniteMeasure P]
  {F : Filtration ℝ≥0 mΩ} [SigmaFiniteFiltration P F] {X : ℝ≥0 → Ω → ℝ}

theorem IsContinuousLocalMartingale.isComplexLocalMartingale_characteristicExponential
    (hM : IsContinuousLocalMartingale X F P) (hF : F.IsUsual P) (u : ℝ) :
    IsComplexLocalMartingale ((hM.isSemimartingale hF).characteristicExponential hF u) F P := by
  let hX := hM.isSemimartingale hF
  let E := hX.characteristicExponential hF u
  let hE := hX.isComplexSemimartingale_characteristicExponential hF u
  let haL := Adapted.complexLeftLimitProcess_of_usual hE.adapted hF hE.hasCadlagPaths
  let hrL := hE.hasCadlagPaths.hasCagladPaths_complexLeftLimitProcess
  have hJ := hX.isComplexLocalMartingale_complexIntegrandIntegral hF
    (hM.locally_squareIntegrableMartingale hF) haL hrL
  have hI := isComplexLocalMartingale_const_initial (P := P) (hE.adapted 0)
  have he : Indistinguishable
      ((fun (_ : ℝ≥0) ω ↦ E 0 ω) +
        fun t ω ↦ (Complex.I * (u : ℂ)) * hX.complexIntegrandIntegral hF haL hrL t ω) E P := by
    filter_upwards [hX.characteristicExponential_sub_initial_eq_integral hF hM.2 u]
      with ω heω t
    change E 0 ω + Complex.I * (u : ℂ) * hX.complexIntegrandIntegral hF haL hrL t ω = E t ω
    calc
      _ = Complex.I * (u : ℂ) * hX.complexIntegrandIntegral hF haL hrL t ω + E 0 ω :=
        add_comm _ _
      _ = _ := (eq_add_of_sub_eq (heω t)).symm
  exact (hI.add (hJ.const_mul hF (Complex.I * (u : ℂ))) hF).congr hF hE.adapted he

theorem IsContinuousLocalMartingale.martingale_characteristicExponential_of_bracket_eq_time
    (hM : IsContinuousLocalMartingale X F P) (hF : F.IsUsual P)
    (hq : Indistinguishable ((hM.isSemimartingale hF).continuousQuadraticVariation hF)
      (fun t _ ↦ (t : ℝ)) P) (u : ℝ) :
    Martingale ((hM.isSemimartingale hF).characteristicExponential hF u) F P := by
  apply IsComplexLocalMartingale.martingale_of_integrable_envelope
    (hM.isComplexLocalMartingale_characteristicExponential hF u)
  intro T
  refine ⟨fun _ ↦ Real.exp (((1 / 2 : ℝ) * u ^ 2) * T), integrable_const _, ?_⟩
  filter_upwards [hq] with ω hqω t ht
  rw [IsSemimartingale.norm_characteristicExponential, hqω t]
  exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (by exact_mod_cast ht) (by positivity))

end ProbabilityTheory
