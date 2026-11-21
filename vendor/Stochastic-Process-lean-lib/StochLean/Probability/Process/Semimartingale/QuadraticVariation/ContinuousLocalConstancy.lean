/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.Semimartingale.QuadraticVariation.ContinuousLocalZero
public import StochLean.Probability.Process.Semimartingale.QuadraticVariation.Centering

/-! # Protter II.27: constant raw bracket exactly characterizes constant paths

Centering is performed with the same raw bracket, and the arbitrary initial
random variable need not be integrable. Equalities are indistinguishability
statements, so exceptional sample paths do not count as nonconstant processes.
-/

@[expose] public section

open MeasureTheory
open scoped NNReal

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsFiniteMeasure P]
  {F : Filtration ℝ≥0 mΩ} [SigmaFiniteFiltration P F] {X : ℝ≥0 → Ω → ℝ}

theorem IsContinuousLocalMartingale.indistinguishable_initial_of_quadraticVariation_constant
    (hX : IsContinuousLocalMartingale X F P) (hF : F.IsUsual P)
    (hQ : Indistinguishable ((hX.isSemimartingale hF).quadraticVariation hF)
      (fun _ ω ↦ (X 0 ω) ^ 2) P) :
    Indistinguishable X (fun _ ↦ X 0) P := by
  let hSM := hX.isSemimartingale hF
  have hcenter := hX.sub_initial hF
  have hzero : Indistinguishable ((hcenter.isSemimartingale hF).quadraticVariation hF) 0 P := by
    filter_upwards [hSM.quadraticVariation_sub_initial hF, hQ] with ω hc hq t
    change (hSM.sub (isSemimartingale_const_initial (hSM.adapted 0))).quadraticVariation hF t ω = 0
    rw [hc t, hq t, sub_self]
  filter_upwards [hcenter.indistinguishable_zero_of_quadraticVariation_zero hF hzero] with ω hω t
  exact sub_eq_zero.mp (hω t)

theorem IsContinuousLocalMartingale.quadraticVariation_eq_initial_iff_constant
    (hX : IsContinuousLocalMartingale X F P) (hF : F.IsUsual P) :
    Indistinguishable ((hX.isSemimartingale hF).quadraticVariation hF)
        (fun _ ω ↦ (X 0 ω) ^ 2) P ↔
      Indistinguishable X (fun _ ↦ X 0) P := by
  refine ⟨hX.indistinguishable_initial_of_quadraticVariation_constant hF, ?_⟩
  intro hc
  exact ((hX.isSemimartingale hF).quadraticVariation_congr
    (isSemimartingale_const_initial (hX.1.1 0)) hF hc).trans
      (quadraticVariation_const_initial (hX.1.1 0) hF)

end ProbabilityTheory
