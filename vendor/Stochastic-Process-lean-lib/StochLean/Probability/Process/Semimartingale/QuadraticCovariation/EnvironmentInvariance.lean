/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.Semimartingale.QuadraticCovariation
public import StochLean.Probability.Process.Semimartingale.StochasticIntegral.AbsoluteContinuity
public import StochLean.Probability.Process.Semimartingale.StochasticIntegral.FiltrationInvariance

/-! # Environment invariance of the actual raw quadratic brackets

The existing Chapter II integral is invariant under absolutely continuous
changes of measure and under changes between two usual filtrations in which
the original source is a semimartingale. Its defining square identity then
gives invariance of raw quadratic variation; actual polarization gives the
mixed statement. The original initial square and product are retained.

For a measure change, the target semimartingale property is constructed from
absolute continuity. Target usuality remains explicit. For a filtration
change, neither filtration inclusion nor a semimartingale property under
their generated union is assumed.

These results concern only the raw brackets. Predictable compensators can
change with the measure or filtration and may cease to exist after a measure
change; no corresponding unconditional angle-bracket invariance is claimed.
-/

@[expose] public section

open MeasureTheory Filter
open scoped NNReal

namespace ProbabilityTheory.IsSemimartingale

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsFiniteMeasure P]
  {F G : Filtration ℝ≥0 mΩ} {X Y : ℝ≥0 → Ω → ℝ}

section MeasureChange

variable {Q : Measure Ω} [IsFiniteMeasure Q]

/-- Actual raw quadratic variation is unchanged almost surely for an
absolutely continuous target measure, on its explicitly usual filtration. -/
theorem quadraticVariation_absolutelyContinuous
    (hX : IsSemimartingale X F P) (hQP : Q ≪ P)
    (hFP : F.IsUsual P) (hFQ : F.IsUsual Q) :
    Indistinguishable ((hX.absolutelyContinuous hQP hFP).quadraticVariation hFQ)
      (hX.quadraticVariation hFP) Q := by
  have he := hX.stochasticIntegral_absolutelyContinuous hQP hFP hFQ
    (hX.adapted.leftLimitProcess_of_usual hFP hX.hasCadlagPaths)
    hX.hasCadlagPaths.hasCagladPaths_leftLimitProcess
  filter_upwards [he] with ω hω t
  simp only [quadraticVariation, hω t]

/-- Actual raw mixed covariation is measure-invariant by polarization.
The target semimartingales are derived rather than supplied as extra data. -/
theorem quadraticCovariation_absolutelyContinuous
    (hX : IsSemimartingale X F P) (hY : IsSemimartingale Y F P) (hQP : Q ≪ P)
    (hFP : F.IsUsual P) (hFQ : F.IsUsual Q) :
    Indistinguishable
      ((hX.absolutelyContinuous hQP hFP).quadraticCovariation
        (hY.absolutelyContinuous hQP hFP) hFQ)
      (hX.quadraticCovariation hY hFP) Q := by
  filter_upwards [(hX.add hY).quadraticVariation_absolutelyContinuous hQP hFP hFQ,
    hX.quadraticVariation_absolutelyContinuous hQP hFP hFQ,
    hY.quadraticVariation_absolutelyContinuous hQP hFP hFQ] with ω hsum hx hy t
  simp only [quadraticCovariation, hsum t, hx t, hy t]

end MeasureChange

/-- Two usual semimartingale filtrations give indistinguishable actual raw
quadratic variations, without requiring either filtration to contain the other. -/
theorem quadraticVariation_congr_filtration
    (hXF : IsSemimartingale X F P) (hXG : IsSemimartingale X G P)
    (hF : F.IsUsual P) (hG : G.IsUsual P) :
    Indistinguishable (hXF.quadraticVariation hF) (hXG.quadraticVariation hG) P := by
  have he := hXF.stochasticIntegral_congr_filtration hXG hF hG
    (hXF.adapted.leftLimitProcess_of_usual hF hXF.hasCadlagPaths)
    (hXG.adapted.leftLimitProcess_of_usual hG hXG.hasCadlagPaths)
    hXF.hasCadlagPaths.hasCagladPaths_leftLimitProcess
  filter_upwards [he] with ω hω t
  simp only [quadraticVariation, hω t]

/-- Raw mixed covariation is invariant when both original processes are
semimartingales for each of the two usual filtrations. -/
theorem quadraticCovariation_congr_filtration
    (hXF : IsSemimartingale X F P) (hYF : IsSemimartingale Y F P)
    (hXG : IsSemimartingale X G P) (hYG : IsSemimartingale Y G P)
    (hF : F.IsUsual P) (hG : G.IsUsual P) :
    Indistinguishable (hXF.quadraticCovariation hYF hF)
      (hXG.quadraticCovariation hYG hG) P := by
  filter_upwards [(hXF.add hYF).quadraticVariation_congr_filtration (hXG.add hYG) hF hG,
    hXF.quadraticVariation_congr_filtration hXG hF hG,
    hYF.quadraticVariation_congr_filtration hYG hF hG] with ω hsum hx hy t
  simp only [quadraticCovariation, hsum t, hx t, hy t]

end ProbabilityTheory.IsSemimartingale
