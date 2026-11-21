/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.Semimartingale.Quasimartingale.RaoCoordinates
public import StochLean.Probability.Martingale.Convergence.RegularizationSupermartingale

/-! # The positive-supermartingale difference theorem

Protter III.17, printed pages 118--119, characterizes quasimartingales on the
whole half-line as differences of nonnegative right-continuous supermartingales.
The artificial terminal-zero convention belongs to the existing conditional
variation owner; no actual value or limit at infinity is introduced here.

The actual future partition envelopes first give supermartingale coordinates.
Their canonical dyadic right limits remain supermartingales and have cadlag
paths. The difference agrees indistinguishably with the right-continuous source,
although neither coordinate is assumed to be its own right-limit modification.
Replacing the positive coordinate by the source plus the negative coordinate
makes the final decomposition an exact function identity.

This is III.17, not the subsequent III.18 theorem named Rao's theorem in the
book, whose conclusion involves a local martingale and predictable variation.
-/

@[expose] public section

open MeasureTheory Filter
open scoped NNReal ENNReal

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsFiniteMeasure P]
  {F : Filtration ℝ≥0 mΩ} {X : ℝ≥0 → Ω → ℝ}

/-- Protter III.17, existence with cadlag coordinates and the original global
conditional-variation bound for each coordinate's first moment. The source
identity is exact, while nonnegativity holds on one common full-measure event. -/
theorem IsQuasimartingale.exists_nonnegative_cadlag_supermartingale_decomposition
    (hX : IsQuasimartingale X F P) (hF : F.IsUsual P) :
    ∃ Y Z : ℝ≥0 → Ω → ℝ,
      Supermartingale Y F P ∧ Supermartingale Z F P ∧
      HasCadlagPaths Y P ∧ HasCadlagPaths Z P ∧
      (∀ᵐ ω ∂P, ∀ t, 0 ≤ Y t ω ∧ 0 ≤ Z t ω) ∧ X = Y - Z ∧
      (∀ t, (∫ ω, Y t ω ∂P) ≤ (eConditionalVariation X F P).toReal) ∧
      (∀ t, (∫ ω, Z t ω ∂P) ≤ (eConditionalVariation X F P).toReal) := by
  obtain ⟨U, V, hU, hV, hn, he, hbU, hbV⟩ :=
    exists_nonnegative_supermartingale_coordinates_of_finiteConditionalVariation
      hX.adapted hX.integrable hX.hasFiniteConditionalVariation
  let Z := dyadicRightLimitProcess V
  let Y := X + Z
  have hR : Supermartingale (dyadicRightLimitProcess U) F P :=
    hU.supermartingale_dyadicRightLimitProcess hF
  have hZ : Supermartingale Z F P := hV.supermartingale_dyadicRightLimitProcess hF
  have heR : Indistinguishable (dyadicRightLimitProcess U - Z) X P :=
    hU.indistinguishable_sub_dyadicRightLimitProcess hV
      hX.hasCadlagPaths.hasRightContinuousPaths he
  have heY : Indistinguishable (dyadicRightLimitProcess U) Y P := by
    filter_upwards [heR] with ω hω t
    exact eq_add_of_sub_eq (hω t)
  have hY : Supermartingale Y F P :=
    hR.congr (hX.adapted.stronglyAdapted.add hZ.stronglyAdapted)
      (fun t ↦ heY.mono fun _ hω ↦ hω t)
  have hcZ : HasCadlagPaths Z P := hV.hasCadlagPaths_dyadicRightLimitProcess
  have hcY : HasCadlagPaths Y P := hX.hasCadlagPaths.add hcZ
  have hnR := hU.ae_forall_nonneg_dyadicRightLimitProcess
    (fun t ↦ Eventually.of_forall fun ω ↦ (hn t ω).1)
  have hnZ := hV.ae_forall_nonneg_dyadicRightLimitProcess
    (fun t ↦ Eventually.of_forall fun ω ↦ (hn t ω).2)
  have hnYZ : ∀ᵐ ω ∂P, ∀ t, 0 ≤ Y t ω ∧ 0 ≤ Z t ω := by
    filter_upwards [hnR, hnZ, heY] with ω hrω hzω heω t
    exact ⟨(hrω t).trans_eq (heω t), hzω t⟩
  refine ⟨Y, Z, hY, hZ, hcY, hcZ, hnYZ, ?_, ?_, ?_⟩
  · funext t ω
    change X t ω = (X t ω + Z t ω) - Z t ω
    ring
  · intro t
    calc
      (∫ ω, Y t ω ∂P) = ∫ ω, dyadicRightLimitProcess U t ω ∂P :=
        integral_congr_ae (heY.symm.mono fun _ hω ↦ hω t)
      _ ≤ ∫ ω, U t ω ∂P := integral_mono_ae (hR.integrable t) (hU.integrable t)
        (hU.dyadicRightLimitProcess_ae_le hF t)
      _ ≤ (eConditionalVariation X F P).toReal := hbU t
  · intro t
    exact (integral_mono_ae (hZ.integrable t) (hV.integrable t)
      (hV.dyadicRightLimitProcess_ae_le hF t)).trans (hbV t)

/-- Protter III.17: the existing quasimartingale predicate is equivalent to
an exact difference of two nonnegative cadlag supermartingales. -/
theorem isQuasimartingale_iff_exists_nonnegative_cadlag_supermartingales
    (hF : F.IsUsual P) :
    IsQuasimartingale X F P ↔ ∃ Y Z : ℝ≥0 → Ω → ℝ,
      Supermartingale Y F P ∧ Supermartingale Z F P ∧
      HasCadlagPaths Y P ∧ HasCadlagPaths Z P ∧
      (∀ᵐ ω ∂P, ∀ t, 0 ≤ Y t ω ∧ 0 ≤ Z t ω) ∧ X = Y - Z := by
  constructor
  · intro hX
    obtain ⟨Y, Z, hY, hZ, hcY, hcZ, hn, he, _, _⟩ :=
      hX.exists_nonnegative_cadlag_supermartingale_decomposition hF
    exact ⟨Y, Z, hY, hZ, hcY, hcZ, hn, he⟩
  · rintro ⟨Y, Z, hY, hZ, hcY, hcZ, hn, rfl⟩
    exact hY.isQuasimartingale_sub_of_nonneg hZ hF
      hcY.hasRightContinuousPaths hcZ.hasRightContinuousPaths
      (fun t ↦ hn.mono fun _ hω ↦ (hω t).1)
      (fun t ↦ hn.mono fun _ hω ↦ (hω t).2)

end ProbabilityTheory
