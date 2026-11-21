/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.Semimartingale.QuadraticVariation.ContinuousPartAlgebra
public import StochLean.Probability.Process.Semimartingale.QuadraticVariation.Stopping
public import StochLean.Analysis.PathVariation.StieltjesStopping

/-! # Stopping the continuous component of the raw square bracket

Raw-bracket stopping identifies the genuine Stieltjes paths. Point-diffuse
restriction then proves the continuous-part identity, for zero, finite and
infinite stopping times without an initial integrability assumption.
-/

@[expose] public section

open MeasureTheory StochLean Set
open scoped NNReal

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsFiniteMeasure P]
  {F : Filtration ℝ≥0 mΩ} {X : ℝ≥0 → Ω → ℝ}

theorem IsSemimartingale.continuousQuadraticVariation_stoppedProcess
    (hX : IsSemimartingale X F P) (hF : F.IsUsual P)
    {τ : Ω → WithTop ℝ≥0} (hτ : IsStoppingTime F τ) :
    Indistinguishable ((hX.stoppedProcess hF hτ).continuousQuadraticVariation hF)
      (MeasureTheory.stoppedProcess (hX.continuousQuadraticVariation hF) τ) P := by
  let D := Classical.choice (hX.nonempty_bracketRealization hX hF)
  let E := Classical.choice ((hX.stoppedProcess hF hτ).nonempty_bracketRealization
    (hX.stoppedProcess hF hτ) hF)
  filter_upwards [D.left_eq, E.left_eq, hX.quadraticVariation_stoppedProcess hF hτ]
    with ω hd he hs t
  change stieltjesContinuousPart (E.left ω) t =
    stieltjesContinuousPart (D.left ω) ((min (t : WithTop ℝ≥0) (τ ω)).untopA)
  cases hτω : τ ω with
  | top =>
    have heq : E.left ω = D.left ω := by
      apply StieltjesFunction.ext
      intro u
      have hv := (he u).symm.trans (hs u)
      simpa only [MeasureTheory.stoppedProcess, hτω, min_eq_left le_top,
        WithTop.untopA, WithTop.untopD_coe, hd] using hv
    simp only [heq, min_eq_left le_top, WithTop.untopA, WithTop.untopD_coe]
  | coe a =>
    have heq : E.left ω = stieltjesStop (D.left ω) a := by
      apply StieltjesFunction.ext
      intro u
      have hv := (he u).symm.trans (hs u)
      simpa only [MeasureTheory.stoppedProcess, hτω, ← WithTop.coe_min,
        WithTop.untopA, WithTop.untopD_coe, hd, stieltjesStop_apply] using hv
    simp only [heq, ← WithTop.coe_min, WithTop.untopA, WithTop.untopD_coe,
      stieltjesContinuousPart_stop]

end ProbabilityTheory
