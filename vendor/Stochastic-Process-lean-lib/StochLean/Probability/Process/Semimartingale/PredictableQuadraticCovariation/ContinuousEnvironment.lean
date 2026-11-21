/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.Semimartingale.PredictableQuadraticCovariation.Continuous
public import StochLean.Probability.Process.Semimartingale.QuadraticCovariation.EnvironmentInvariance

/-! # Environment invariance of angles with one continuous source

General predictable compensators need not be invariant under a change of
measure or filtration. A continuous argument is a genuine sufficient
condition for mixed quadratic brackets: in each environment the actual
angle domain is constructed, and the selected angle is the raw bracket
minus the same original initial product. Actual raw environment invariance
therefore identifies the angles.

Only one source is required to be continuous. No local-L2 property, square
angle domain for the other source, proposed target compensator, or target
remainder martingale is assumed. Target usual conditions remain explicit.
-/

@[expose] public section

open MeasureTheory Filter
open scoped NNReal

namespace ProbabilityTheory.IsSemimartingale

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
  {F G : Filtration ℝ≥0 mΩ} {X Y : ℝ≥0 → Ω → ℝ}

/-- With one continuous source, both actual mixed-angle domains and the
target semimartingales are constructed under an absolutely continuous
probability measure. The comparison holds almost surely for that target. -/
theorem predictableQuadraticCovariation_absolutelyContinuous_of_left_continuous
    {Q : Measure Ω} [IsProbabilityMeasure Q]
    (hX : IsSemimartingale X F P) (hY : IsSemimartingale Y F P) (hQP : Q ≪ P)
    (hFP : F.IsUsual P) (hFQ : F.IsUsual Q) (hc : HasContinuousPaths X P) :
    let hXQ := hX.absolutelyContinuous hQP hFP
    let hYQ := hY.absolutelyContinuous hQP hFP
    let hcQ : HasContinuousPaths X Q := hQP.ae_le hc
    Indistinguishable
      (hXQ.predictableQuadraticCovariation hYQ hFQ
        (hXQ.hasLocallyIntegrableVariation_quadraticCovariation_of_left_continuous hYQ hFQ hcQ))
      (hX.predictableQuadraticCovariation hY hFP
        (hX.hasLocallyIntegrableVariation_quadraticCovariation_of_left_continuous
          hY hFP hc)) Q := by
  intro hXQ hYQ hcQ
  filter_upwards [hXQ.predictableQuadraticCovariation_eq_continuous_of_left_continuous
      hYQ hFQ hcQ,
    hQP.ae_le (hX.predictableQuadraticCovariation_eq_continuous_of_left_continuous hY hFP hc),
    hXQ.continuousQuadraticCovariation_eq_of_left_continuous hYQ hFQ hcQ,
    hQP.ae_le (hX.continuousQuadraticCovariation_eq_of_left_continuous hY hFP hc),
    hX.quadraticCovariation_absolutelyContinuous hY hQP hFP hFQ] with ω hQ hP hCQ hCP hraw t
  rw [hQ t, hP t, hCQ t, hCP t, hraw t]

/-- One AE-continuous argument suffices for actual angle invariance between
two usual semimartingale filtrations. Neither filtration need contain the
other, and all required local-variation domains are genuinely derived. -/
theorem predictableQuadraticCovariation_congr_filtration_of_left_continuous
    (hXF : IsSemimartingale X F P) (hYF : IsSemimartingale Y F P)
    (hXG : IsSemimartingale X G P) (hYG : IsSemimartingale Y G P)
    (hF : F.IsUsual P) (hG : G.IsUsual P) (hc : HasContinuousPaths X P) :
    Indistinguishable
      (hXF.predictableQuadraticCovariation hYF hF
        (hXF.hasLocallyIntegrableVariation_quadraticCovariation_of_left_continuous hYF hF hc))
      (hXG.predictableQuadraticCovariation hYG hG
        (hXG.hasLocallyIntegrableVariation_quadraticCovariation_of_left_continuous
          hYG hG hc)) P := by
  filter_upwards [hXF.predictableQuadraticCovariation_eq_continuous_of_left_continuous hYF hF hc,
    hXG.predictableQuadraticCovariation_eq_continuous_of_left_continuous hYG hG hc,
    hXF.continuousQuadraticCovariation_eq_of_left_continuous hYF hF hc,
    hXG.continuousQuadraticCovariation_eq_of_left_continuous hYG hG hc,
    hXF.quadraticCovariation_congr_filtration hYF hXG hYG hF hG] with ω hAF hAG hCF hCG hraw t
  rw [hAF t, hAG t, hCF t, hCG t, hraw t]

end ProbabilityTheory.IsSemimartingale
