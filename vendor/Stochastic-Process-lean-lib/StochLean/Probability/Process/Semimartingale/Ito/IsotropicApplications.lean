/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.Semimartingale.Ito.SubharmonicOpenDomain
public import StochLean.Probability.Process.Semimartingale.QuadraticCovariation.OrthogonalClock

/-! # Protter II.41 with the source raw-bracket convention

The common raw clock need not start at zero: its initial value is removed
when passing to the continuous bracket. Harmonic functions are treated on an
arbitrary open domain. The subharmonic interfaces state the classical C2
nonnegative-Laplacian hypothesis and distinguish masked locality from true
submartingales. No nonsmooth potential-theoretic extension is asserted.
-/

@[expose] public section

open MeasureTheory InnerProductSpace WithLp
open scoped NNReal

namespace ProbabilityTheory

theorem protter_harmonic_composition
    {ι Ω : Type*} [Fintype ι] {mΩ : MeasurableSpace Ω}
    {P : Measure Ω} [IsProbabilityMeasure P] {F : Filtration ℝ≥0 mΩ}
    {X : ι → ℝ≥0 → Ω → ℝ} {A : ℝ≥0 → Ω → ℝ} {f : EuclideanSpace ℝ ι → ℝ}
    (hX : ∀ i, IsContinuousLocalMartingale (X i) F P) (hF : F.IsUsual P)
    (hd : ∀ i, Indistinguishable (((hX i).isSemimartingale hF).quadraticVariation hF) A P)
    (ho : ∀ i j, i ≠ j → Indistinguishable
      (((hX i).isSemimartingale hF).quadraticCovariation ((hX j).isSemimartingale hF) hF) 0 P)
    {D : Set (EuclideanSpace ℝ ι)} (hD : IsOpen D) (hf : HarmonicOnNhd f D)
    (hstay : ∀ᵐ ω ∂P, ∀ t, toLp 2 (fun i ↦ X i t ω) ∈ D) :
    IsContinuousLocalMartingale (fun t ω ↦ f (toLp 2 (fun i ↦ X i t ω))) F P := by
  have h := continuous_brackets_of_raw_orthogonal_clock_centered
    (fun i ↦ (hX i).isSemimartingale hF) hF (fun i ↦ (hX i).2) hd ho
  exact isContinuousLocalMartingale_comp_harmonic_on_open_of_isotropic
    hX hF h.1 h.2 hD hf hstay

theorem protter_harmonic_composition_of_integrable_envelope
    {ι Ω : Type*} [Fintype ι] {mΩ : MeasurableSpace Ω}
    {P : Measure Ω} [IsProbabilityMeasure P] {F : Filtration ℝ≥0 mΩ}
    {X : ι → ℝ≥0 → Ω → ℝ} {A : ℝ≥0 → Ω → ℝ} {f : EuclideanSpace ℝ ι → ℝ}
    (hX : ∀ i, IsContinuousLocalMartingale (X i) F P) (hF : F.IsUsual P)
    (hd : ∀ i, Indistinguishable (((hX i).isSemimartingale hF).quadraticVariation hF) A P)
    (ho : ∀ i j, i ≠ j → Indistinguishable
      (((hX i).isSemimartingale hF).quadraticCovariation ((hX j).isSemimartingale hF) hF) 0 P)
    {D : Set (EuclideanSpace ℝ ι)} (hD : IsOpen D) (hf : HarmonicOnNhd f D)
    (hstay : ∀ᵐ ω ∂P, ∀ t, toLp 2 (fun i ↦ X i t ω) ∈ D)
    (hdom : ∀ T : ℝ≥0, ∃ R : Ω → ℝ, Integrable R P ∧
      ∀ᵐ ω ∂P, ∀ t ≤ T, ‖f (toLp 2 (fun i ↦ X i t ω))‖ ≤ R ω) :
    Martingale (fun t ω ↦ f (toLp 2 (fun i ↦ X i t ω))) F P :=
  (protter_harmonic_composition hX hF hd ho hD hf hstay).1.martingale_of_integrable_envelope hdom

theorem protter_subharmonic_composition_locally
    {ι Ω : Type*} [Fintype ι] {mΩ : MeasurableSpace Ω}
    {P : Measure Ω} [IsProbabilityMeasure P] {F : Filtration ℝ≥0 mΩ}
    {X : ι → ℝ≥0 → Ω → ℝ} {A : ℝ≥0 → Ω → ℝ} {f : EuclideanSpace ℝ ι → ℝ}
    (hX : ∀ i, IsContinuousLocalMartingale (X i) F P) (hF : F.IsUsual P)
    (hd : ∀ i, Indistinguishable (((hX i).isSemimartingale hF).quadraticVariation hF) A P)
    (ho : ∀ i j, i ≠ j → Indistinguishable
      (((hX i).isSemimartingale hF).quadraticCovariation ((hX j).isSemimartingale hF) hF) 0 P)
    {D : Set (EuclideanSpace ℝ ι)} (hD : IsOpen D) (hf : ContDiffOn ℝ 2 f D)
    (hlap : ∀ x ∈ D, 0 ≤ Laplacian.laplacian f x)
    (hstay : ∀ᵐ ω ∂P, ∀ t, toLp 2 (fun i ↦ X i t ω) ∈ D) :
    Locally (fun Y ↦ Submartingale Y F P) F
      (fun t ω ↦ f (toLp 2 (fun i ↦ X i t ω))) P := by
  have h := continuous_brackets_of_raw_orthogonal_clock_centered
    (fun i ↦ (hX i).isSemimartingale hF) hF (fun i ↦ (hX i).2) hd ho
  exact locally_submartingale_comp_laplacian_nonneg_on_open_of_isotropic
    hX hF h.1 h.2 hD hf hlap hstay

theorem protter_subharmonic_composition_of_integrable_envelope
    {ι Ω : Type*} [Fintype ι] {mΩ : MeasurableSpace Ω}
    {P : Measure Ω} [IsProbabilityMeasure P] {F : Filtration ℝ≥0 mΩ}
    {X : ι → ℝ≥0 → Ω → ℝ} {A : ℝ≥0 → Ω → ℝ} {f : EuclideanSpace ℝ ι → ℝ}
    (hX : ∀ i, IsContinuousLocalMartingale (X i) F P) (hF : F.IsUsual P)
    (hd : ∀ i, Indistinguishable (((hX i).isSemimartingale hF).quadraticVariation hF) A P)
    (ho : ∀ i j, i ≠ j → Indistinguishable
      (((hX i).isSemimartingale hF).quadraticCovariation ((hX j).isSemimartingale hF) hF) 0 P)
    {D : Set (EuclideanSpace ℝ ι)} (hD : IsOpen D) (hf : ContDiffOn ℝ 2 f D)
    (hlap : ∀ x ∈ D, 0 ≤ Laplacian.laplacian f x)
    (hstay : ∀ᵐ ω ∂P, ∀ t, toLp 2 (fun i ↦ X i t ω) ∈ D)
    (hdom : ∀ T : ℝ≥0, ∃ R : Ω → ℝ, Integrable R P ∧
      ∀ᵐ ω ∂P, ∀ t ≤ T, ‖f (toLp 2 (fun i ↦ X i t ω))‖ ≤ R ω) :
    Submartingale (fun t ω ↦ f (toLp 2 (fun i ↦ X i t ω))) F P := by
  have h := continuous_brackets_of_raw_orthogonal_clock_centered
    (fun i ↦ (hX i).isSemimartingale hF) hF (fun i ↦ (hX i).2) hd ho
  exact submartingale_comp_laplacian_nonneg_on_open_of_isotropic_of_integrable_envelope
    hX hF h.1 h.2 hD hf hlap hstay hdom

end ProbabilityTheory
