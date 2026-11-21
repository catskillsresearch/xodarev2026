/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.FiniteVariation.PredictableBoundedVariation
public import StochLean.Probability.Process.FiniteVariation.PredictableBoundedVariationCovariation
public import StochLean.Probability.Process.Semimartingale.QuadraticCovariation.InitialMask
public import StochLean.Probability.Process.Semimartingale.QuadraticCovariation.Stopping
public import StochLean.Probability.Process.LocalMartingale.Localization
public import StochLean.Probability.Process.LocalMartingale.InitialValue
public import StochLean.Probability.Process.LocalMartingale.Reducing

/-! # Yoeurp's lemma for the actual raw quadratic covariation

A predictable cadlag FV process has native localizations with deterministic
whole-variation budgets. On each level, the martingale's actual UI localizers
reduce the centered raw covariation to the proved predictable-jump series.
The arbitrary initial product is a constant native local martingale, not an
implicitly integrable random variable. Adding it back recovers the raw bracket.

Actual simultaneous stopping and initial-mask identities transfer these
conclusions to localizations of the original raw covariation. Native iterated
localization closes both levels. No initial moments, square integrability,
bounded martingale, or integrable variation assumption is imposed on the source.
-/

@[expose] public section

open ProbabilityTheory Filter Set
open scoped NNReal ENNReal

namespace MeasureTheory.IsStronglyPredictable

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
  {F : Filtration ℝ≥0 mΩ} {A M : ℝ≥0 → Ω → ℝ}

private theorem quadraticCovariation_masked_stoppedProcess
    (hM : IsSemimartingale M F P) (hA : IsSemimartingale A F P) (hF : F.IsUsual P)
    {τ : Ω → WithTop ℝ≥0} (hτ : IsStoppingTime F τ) :
    Indistinguishable
      (((hM.indicator_initial (hτ.measurableSet_gt 0)).stoppedProcess hF hτ).quadraticCovariation
        ((hA.indicator_initial (hτ.measurableSet_gt 0)).stoppedProcess hF hτ) hF)
      (MeasureTheory.stoppedProcess (fun t ↦ {ω | 0 < τ ω}.indicator
        (hM.quadraticCovariation hA hF t)) τ) P :=
  ((hM.indicator_initial (hτ.measurableSet_gt 0)).quadraticCovariation_stoppedProcess_both
    (hA.indicator_initial (hτ.measurableSet_gt 0)) hF hτ).trans
    ((hM.quadraticCovariation_indicator_initial hA hF (hτ.measurableSet_gt 0)).stoppedProcess τ)

private theorem isLocalMartingale_quadraticCovariation_of_variation_bound
    (hA : IsStronglyPredictable F A) (hF : F.IsUsual P) (hcA : HasCadlagPaths A P)
    (hv : HasFiniteVariationPaths A P) (C : ℝ) (hC : 0 ≤ C)
    (hb : ∀ᵐ ω ∂P, eVariationOn (A · ω) univ ≤ ENNReal.ofReal C)
    (hM : IsLocalMartingale M F P) :
    IsLocalMartingale ((hM.isSemimartingale hF).quadraticCovariation
      (hv.isSemimartingale hA.stronglyAdapted.adapted hF hcA) hF) F P := by
  let hSM := hM.isSemimartingale hF
  let hSA := hv.isSemimartingale hA.stronglyAdapted.adapted hF hcA
  have haQ := hSM.adapted_quadraticCovariation hSA hF
  have hcQ := hSM.hasCadlagPaths_quadraticCovariation hSA hF
  apply isLocalMartingale_of_locally_localMartingale hF hcQ
  obtain ⟨τ, hτ, hu⟩ := hM.locally_cadlagUI
  refine ⟨τ, hτ, fun n ↦ ?_⟩
  let MN := MeasureTheory.stoppedProcess (fun t ↦ {ω | 0 < τ n ω}.indicator (M t)) (τ n)
  let AN := MeasureTheory.stoppedProcess (fun t ↦ {ω | 0 < τ n ω}.indicator (A t)) (τ n)
  have hAN := isStable_predictable_cadlag_boundedTotalVariation (F := F) (P := P)
    A ⟨hA, hcA, C, hC, hb⟩ (τ n) (hτ.isStoppingTime n)
  obtain ⟨hpAN, hcAN, D, hD, hbAN⟩ := hAN
  have hfinAN : HasFiniteTotalVariationPaths AN P :=
    hbAN.mono fun _ hω ↦ ne_top_of_le_ne_top ENNReal.ofReal_ne_top hω
  have hvAN := hfinAN.hasFiniteVariationPaths
  have huMN : IsUIMartingale MN F P := (hu n).1
  have hcMN : HasCadlagPaths MN P := (hu n).2
  let hSMN := (huMN.isLocalMartingale hcMN).isSemimartingale hF
  let hSAN := hvAN.isSemimartingale hpAN.stronglyAdapted.adapted hF hcAN
  have huQ : IsUIMartingale
      (hSMN.quadraticCovariation hSAN hF - fun _ ω ↦ MN 0 ω * AN 0 ω) F P :=
    hpAN.isUIMartingale_centered_quadraticCovariation_of_variation_bound
      hF hcAN hvAN D hD hbAN huMN hcMN
  have hinit : IsContinuousLocalMartingale (fun _ : ℝ≥0 ↦ fun ω ↦ MN 0 ω * AN 0 ω) F P :=
    isContinuousLocalMartingale_const_initial ((hSMN.adapted 0).mul (hSAN.adapted 0))
  have hcCentered : HasCadlagPaths
      (hSMN.quadraticCovariation hSAN hF - fun _ ω ↦ MN 0 ω * AN 0 ω) P :=
    (hSMN.hasCadlagPaths_quadraticCovariation hSAN hF).sub hinit.2.hasCadlagPaths
  have hraw : IsLocalMartingale (hSMN.quadraticCovariation hSAN hF) F P := by
    simpa only [sub_add_cancel] using (huQ.isLocalMartingale hcCentered).add hinit.1 hF
  have haMask := haQ.indicator_initial ((hτ.isStoppingTime n).measurableSet_gt 0)
  exact hraw.congr hF
    (haMask.stronglyAdapted.stoppedProcess_of_usual hF
      (hcQ.indicator {ω | 0 < τ n ω}).hasRightContinuousPaths (hτ.isStoppingTime n)).adapted
    (quadraticCovariation_masked_stoppedProcess hSM hSA hF (hτ.isStoppingTime n))

/-- Yoeurp's lemma: the actual raw covariation of a local martingale and
a predictable cadlag FV process is a native local martingale. Its initial
product is retained, with no initial integrability or normalization assumption. -/
theorem isLocalMartingale_quadraticCovariation
    (hA : IsStronglyPredictable F A) (hF : F.IsUsual P) (hcA : HasCadlagPaths A P)
    (hv : HasFiniteVariationPaths A P) (hM : IsLocalMartingale M F P) :
    IsLocalMartingale ((hM.isSemimartingale hF).quadraticCovariation
      (hv.isSemimartingale hA.stronglyAdapted.adapted hF hcA) hF) F P := by
  let hSM := hM.isSemimartingale hF
  let hSA := hv.isSemimartingale hA.stronglyAdapted.adapted hF hcA
  have haQ := hSM.adapted_quadraticCovariation hSA hF
  have hcQ := hSM.hasCadlagPaths_quadraticCovariation hSA hF
  apply isLocalMartingale_of_locally_localMartingale hF hcQ
  obtain ⟨τ, hτ, hb⟩ := hA.locally_boundedTotalVariation hF hcA hv
  refine ⟨τ, hτ, fun n ↦ ?_⟩
  let MN := MeasureTheory.stoppedProcess (fun t ↦ {ω | 0 < τ n ω}.indicator (M t)) (τ n)
  let AN := MeasureTheory.stoppedProcess (fun t ↦ {ω | 0 < τ n ω}.indicator (A t)) (τ n)
  obtain ⟨hpAN, hcAN, C, hC, hbAN⟩ := hb n
  have hfinAN : HasFiniteTotalVariationPaths AN P :=
    hbAN.mono fun _ hω ↦ ne_top_of_le_ne_top ENNReal.ofReal_ne_top hω
  have hvAN := hfinAN.hasFiniteVariationPaths
  have hMN : IsLocalMartingale MN F P := hM.masked_stoppedProcess hF (hτ.isStoppingTime n)
  have hraw := isLocalMartingale_quadraticCovariation_of_variation_bound
    hpAN hF hcAN hvAN C hC hbAN hMN
  have haMask := haQ.indicator_initial ((hτ.isStoppingTime n).measurableSet_gt 0)
  exact hraw.congr hF
    (haMask.stronglyAdapted.stoppedProcess_of_usual hF
      (hcQ.indicator {ω | 0 < τ n ω}).hasRightContinuousPaths (hτ.isStoppingTime n)).adapted
    (quadraticCovariation_masked_stoppedProcess hSM hSA hF (hτ.isStoppingTime n))

end MeasureTheory.IsStronglyPredictable
