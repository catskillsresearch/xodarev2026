/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.Semimartingale.BichtelerDellacherie.QuasimartingaleMeasure
public import StochLean.Probability.Process.Semimartingale.Special
public import StochLean.Probability.Process.Semimartingale.MeasureChange.Classical

/-! # The finite-horizon Bichteler--Dellacherie bridge

This file isolates the probabilistic half of the converse theorem.  Once Yan
separation supplies an equivalent probability law, dominated by a finite
multiple of the auxiliary integrability law, the deterministic stop is a
quasimartingale.  Rao gives a special (hence classical) decomposition under
that law, and Girsanov--Meyer transports the classical property back to the
original law.

The functional-analytic construction of the Yan law is deliberately not an
assumption hidden here; it is consumed by the final Bichteler--Dellacherie
module.
-/

@[expose] public section

open MeasureTheory
open scoped NNReal ENNReal

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}
  {F : Filtration ℝ≥0 mΩ} {P R : Measure Ω}
  {X : ℝ≥0 → Ω → ℝ} {T : ℝ≥0}
  [IsProbabilityMeasure P] [IsProbabilityMeasure R]

/-- An equivalent-law quasimartingale decomposition on a deterministic
horizon transfers back to the source probability law. -/
theorem isClassicalSemimartingale_deterministicStoppedProcess_of_equivalent_quasimartingale
    (hRP : R ≪ P) (hPR : P ≪ R)
    (hY : IsQuasimartingale (deterministicStoppedProcess X T) F R)
    (hF : F.IsUsual P) :
    IsClassicalSemimartingale (deterministicStoppedProcess X T) F P := by
  have hFR : F.IsUsual R := hF.of_absolutelyContinuous hPR
  have hclassR :
      IsClassicalSemimartingale (deterministicStoppedProcess X T) F R :=
    (hY.isSpecialSemimartingale hFR).isClassicalSemimartingale
  exact hclassR.equivalentMeasure hPR hRP hFR

/-- The complete finite-horizon probabilistic consumer of a Yan law.  The
law `R` is required to be equivalent to the Lemma 2 law and dominated by a
finite scalar multiple of it; the uniform expectation bound is precisely the
one delivered by separation of the integrable unit elementary-integral
image. -/
theorem EquivalentIntegrabilityMeasure.isClassicalSemimartingale_deterministicStoppedProcess
    (J : EquivalentIntegrabilityMeasure X T P)
    (ha : Adapted F X) (hc : HasCadlagPaths X P)
    (hRJ : R ≪ J.measure) (hJR : J.measure ≪ R)
    {D : ℝ≥0∞} (hD : D ≠ ∞) (hdom : R ≤ D • J.measure)
    {C : ℝ}
    (hbound : ∀ Y ∈ integrableUnitElementaryIntegralSet
      (deterministicStoppedProcess X T) F J.measure,
      (∫ ω, Y ω ∂R) ≤ C)
    (hF : F.IsUsual P) :
    IsClassicalSemimartingale (deterministicStoppedProcess X T) F P := by
  letI : IsProbabilityMeasure J.measure := J.isProbabilityMeasure
  have hRP : R ≪ P := hRJ.trans J.absolutelyContinuous
  have hPR : P ≪ R := J.sourceAbsolutelyContinuous.trans hJR
  have hq : IsQuasimartingale (deterministicStoppedProcess X T) F R :=
    J.isQuasimartingale_deterministicStoppedProcess ha hc hD hdom hbound
  exact
    isClassicalSemimartingale_deterministicStoppedProcess_of_equivalent_quasimartingale
      hRP hPR hq hF

end ProbabilityTheory
