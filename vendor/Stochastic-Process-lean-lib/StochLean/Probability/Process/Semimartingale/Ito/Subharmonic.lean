/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.Semimartingale.Ito.IncreasingDrift
public import StochLean.Probability.Process.Semimartingale.Ito.Harmonic
public import StochLean.Probability.Martingale.LocalSubmartingale

/-! # Corrected full-space subharmonic composition

Nonnegative Laplacian gives a local submartingale, not an unqualified true
submartingale. A common-event integrable envelope on every compact time
interval permits promotion. The Laplacian and locality are the existing
Mathlib owners. `SubharmonicOpenDomain` supplies the classical C2 open-domain
extension and localization; no nonsmooth subharmonic extension is asserted.
-/

@[expose] public section

open MeasureTheory Filter StochLean InnerProductSpace WithLp
open scoped NNReal

namespace ProbabilityTheory

variable {ι Ω : Type*} [Fintype ι] {mΩ : MeasurableSpace Ω}
  {P : Measure Ω} [IsFiniteMeasure P] {F : Filtration ℝ≥0 mΩ}
  {X : ι → ℝ≥0 → Ω → ℝ} {A : ℝ≥0 → Ω → ℝ}

theorem locally_submartingale_comp_of_isotropic_trace_nonneg_on_paths
    [DecidableEq ι] {f : (ι → ℝ) → ℝ}
    (hX : ∀ i, IsContinuousLocalMartingale (X i) F P) (hF : F.IsUsual P)
    (hd : ∀ i, Indistinguishable
      (((hX i).isSemimartingale hF).continuousQuadraticVariation hF) A P)
    (ho : ∀ i j, i ≠ j → Indistinguishable
      (((hX i).isSemimartingale hF).continuousQuadraticCovariation
        ((hX j).isSemimartingale hF) hF) 0 P)
    (hf : ContDiff ℝ 2 f)
    (htrace : ∀ᵐ ω ∂P, ∀ t, 0 ≤ ∑ i, coordinateSecondDeriv f i i (fun j ↦ X j t ω)) :
    Locally (fun Y ↦ Submartingale Y F P) F (fun t ω ↦ f (fun i ↦ X i t ω)) P := by
  classical
  obtain ⟨D, ha, hc, hm, h0, hM⟩ := exists_isotropic_ito_increasing_drift hX hF hd ho hf htrace
  convert hM.1.locally_submartingale_add_of_monotone hF ha hc hm h0 using 1
  funext t ω
  exact (sub_add_cancel _ _).symm

theorem submartingale_comp_of_isotropic_trace_nonneg_of_integrable_envelope
    [DecidableEq ι] {f : (ι → ℝ) → ℝ}
    (hX : ∀ i, IsContinuousLocalMartingale (X i) F P) (hF : F.IsUsual P)
    (hd : ∀ i, Indistinguishable
      (((hX i).isSemimartingale hF).continuousQuadraticVariation hF) A P)
    (ho : ∀ i j, i ≠ j → Indistinguishable
      (((hX i).isSemimartingale hF).continuousQuadraticCovariation
        ((hX j).isSemimartingale hF) hF) 0 P)
    (hf : ContDiff ℝ 2 f)
    (htrace : ∀ᵐ ω ∂P, ∀ t, 0 ≤ ∑ i, coordinateSecondDeriv f i i (fun j ↦ X j t ω))
    (hdom : ∀ T : ℝ≥0, ∃ R : Ω → ℝ, Integrable R P ∧
      ∀ᵐ ω ∂P, ∀ t ≤ T, ‖f (fun i ↦ X i t ω)‖ ≤ R ω) :
    Submartingale (fun t ω ↦ f (fun i ↦ X i t ω)) F P := by
  have ha : Adapted F (fun t ω ↦ f (fun i ↦ X i t ω)) := fun t ↦
    hf.continuous.measurable.comp
      (@measurable_pi_lambda _ _ _ (F t) _ _ (fun i ↦ (hX i).1.1 t))
  exact submartingale_of_locally_submartingale_of_integrable_envelope ha
    (locally_submartingale_comp_of_isotropic_trace_nonneg_on_paths hX hF hd ho hf htrace) hdom

theorem locally_submartingale_comp_laplacian_nonneg_of_isotropic
    {f : EuclideanSpace ℝ ι → ℝ}
    (hX : ∀ i, IsContinuousLocalMartingale (X i) F P) (hF : F.IsUsual P)
    (hd : ∀ i, Indistinguishable
      (((hX i).isSemimartingale hF).continuousQuadraticVariation hF) A P)
    (ho : ∀ i j, i ≠ j → Indistinguishable
      (((hX i).isSemimartingale hF).continuousQuadraticCovariation
        ((hX j).isSemimartingale hF) hF) 0 P)
    (hf : ContDiff ℝ 2 f)
    (hlap : ∀ᵐ ω ∂P, ∀ t, 0 ≤ (Laplacian.laplacian f) (toLp 2 (fun i ↦ X i t ω))) :
    Locally (fun Y ↦ Submartingale Y F P) F
      (fun t ω ↦ f (toLp 2 (fun i ↦ X i t ω))) P := by
  classical
  apply locally_submartingale_comp_of_isotropic_trace_nonneg_on_paths hX hF hd ho
    (hf.comp (PiLp.continuousLinearEquiv 2 ℝ (fun _ : ι ↦ ℝ)).symm.contDiff)
  filter_upwards [hlap] with ω hω t
  change 0 ≤ ∑ i, coordinateSecondDeriv (fun x ↦ f (toLp 2 x)) i i (fun j ↦ X j t ω)
  rw [sum_coordinateSecondDeriv_toLp_eq_laplacian hf]
  exact hω t

theorem submartingale_comp_laplacian_nonneg_of_isotropic_of_integrable_envelope
    {f : EuclideanSpace ℝ ι → ℝ}
    (hX : ∀ i, IsContinuousLocalMartingale (X i) F P) (hF : F.IsUsual P)
    (hd : ∀ i, Indistinguishable
      (((hX i).isSemimartingale hF).continuousQuadraticVariation hF) A P)
    (ho : ∀ i j, i ≠ j → Indistinguishable
      (((hX i).isSemimartingale hF).continuousQuadraticCovariation
        ((hX j).isSemimartingale hF) hF) 0 P)
    (hf : ContDiff ℝ 2 f)
    (hlap : ∀ᵐ ω ∂P, ∀ t, 0 ≤ (Laplacian.laplacian f) (toLp 2 (fun i ↦ X i t ω)))
    (hdom : ∀ T : ℝ≥0, ∃ R : Ω → ℝ, Integrable R P ∧
      ∀ᵐ ω ∂P, ∀ t ≤ T, ‖f (toLp 2 (fun i ↦ X i t ω))‖ ≤ R ω) :
    Submartingale (fun t ω ↦ f (toLp 2 (fun i ↦ X i t ω))) F P := by
  classical
  apply submartingale_comp_of_isotropic_trace_nonneg_of_integrable_envelope hX hF hd ho
    (hf.comp (PiLp.continuousLinearEquiv 2 ℝ (fun _ : ι ↦ ℝ)).symm.contDiff) _ hdom
  filter_upwards [hlap] with ω hω t
  change 0 ≤ ∑ i, coordinateSecondDeriv (fun x ↦ f (toLp 2 x)) i i (fun j ↦ X j t ω)
  rw [sum_coordinateSecondDeriv_toLp_eq_laplacian hf]
  exact hω t

theorem martingale_comp_harmonic_of_isotropic_of_integrable_envelope
    {f : EuclideanSpace ℝ ι → ℝ}
    (hX : ∀ i, IsContinuousLocalMartingale (X i) F P) (hF : F.IsUsual P)
    (hd : ∀ i, Indistinguishable
      (((hX i).isSemimartingale hF).continuousQuadraticVariation hF) A P)
    (ho : ∀ i j, i ≠ j → Indistinguishable
      (((hX i).isSemimartingale hF).continuousQuadraticCovariation
        ((hX j).isSemimartingale hF) hF) 0 P)
    (hf : HarmonicOnNhd f Set.univ)
    (hdom : ∀ T : ℝ≥0, ∃ R : Ω → ℝ, Integrable R P ∧
      ∀ᵐ ω ∂P, ∀ t ≤ T, ‖f (toLp 2 (fun i ↦ X i t ω))‖ ≤ R ω) :
    Martingale (fun t ω ↦ f (toLp 2 (fun i ↦ X i t ω))) F P := by
  have h := isContinuousLocalMartingale_comp_harmonic_of_isotropic hX hF hd ho hf
  exact h.1.martingale_of_integrable_envelope hdom

end ProbabilityTheory
