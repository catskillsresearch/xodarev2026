/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.Semimartingale.Ito.SubharmonicClosedRegion
public import StochLean.Probability.Process.Semimartingale.Ito.HarmonicOpenDomain

/-! # Corrected subharmonic composition on arbitrary open domains

The compact-region exits themselves localize to true submartingales; no
unproved local-submartingale stopping or local-to-local principle is used.
Compact-time integrable domination gives a true submartingale on the full
half-line. Without that guard the conclusion is the actual masked locality.
-/

@[expose] public section

open MeasureTheory Filter Set StochLean InnerProductSpace WithLp
open scoped NNReal

namespace ProbabilityTheory

theorem locally_submartingale_comp_laplacian_nonneg_on_open_of_isotropic
    {ι Ω : Type*} [Fintype ι] {mΩ : MeasurableSpace Ω}
    {P : Measure Ω} [IsProbabilityMeasure P] {F : Filtration ℝ≥0 mΩ}
    {X : ι → ℝ≥0 → Ω → ℝ} {A : ℝ≥0 → Ω → ℝ} {f : EuclideanSpace ℝ ι → ℝ}
    (hX : ∀ i, IsContinuousLocalMartingale (X i) F P) (hF : F.IsUsual P)
    (hd : ∀ i, Indistinguishable
      (((hX i).isSemimartingale hF).continuousQuadraticVariation hF) A P)
    (ho : ∀ i j, i ≠ j → Indistinguishable
      (((hX i).isSemimartingale hF).continuousQuadraticCovariation
        ((hX j).isSemimartingale hF) hF) 0 P)
    {D : Set (EuclideanSpace ℝ ι)} (hD : IsOpen D) (hf : ContDiffOn ℝ 2 f D)
    (hlap : ∀ x ∈ D, 0 ≤ Laplacian.laplacian f x)
    (hstay : ∀ᵐ ω ∂P, ∀ t, toLp 2 (fun i ↦ X i t ω) ∈ D) :
    Locally (fun Y ↦ Submartingale Y F P) F
      (fun t ω ↦ f (toLp 2 (fun i ↦ X i t ω))) P := by
  classical
  obtain ⟨ω₀, hω₀⟩ := hstay.exists
  obtain ⟨K, hK, hKm, hKcover⟩ := exists_compact_exhaustion_with_basepoint hD (hω₀ 0)
  let V := fun t ω ↦ toLp 2 (fun i ↦ X i t ω)
  have haV : Adapted F V := fun t ↦
    (PiLp.continuousLinearEquiv 2 ℝ (fun _ : ι ↦ ℝ)).symm.continuous.measurable.comp
      (@measurable_pi_lambda _ _ _ (F t) _ _ (fun i ↦ (hX i).1.1 t))
  have hcV : HasContinuousPaths V P := by
    filter_upwards [ae_all_iff.2 (fun i ↦ (hX i).2)] with ω hω
    exact (PiLp.continuousLinearEquiv 2 ℝ (fun _ : ι ↦ ℝ)).symm.continuous.comp
      (continuous_pi hω)
  have hcover : ∀ᵐ ω ∂P, ∀ T : ℝ≥0, ∃ N, ∀ n ≥ N, ∀ t ≤ T, V t ω ∈ K n := by
    filter_upwards [hcV, hstay] with ω hω hDω T
    obtain ⟨N, hN⟩ := hKcover ((V · ω) '' Icc 0 T) (isCompact_Icc.image hω)
      (by rintro _ ⟨t, _, rfl⟩; exact hDω t)
    exact ⟨N, fun n hn t ht ↦ hN n hn ⟨t, ⟨bot_le, ht⟩, rfl⟩⟩
  let τ := fun n ↦ hittingAfter V (K n)ᶜ 0
  have hτ : IsLocalizingSequence F τ P := haV.isLocalizingSequence_closedRegion_exits
    hF hcV (fun n ↦ (hK n).1.isClosed) hKm hcover
  refine ⟨τ, hτ, fun n ↦ ?_⟩
  apply submartingale_masked_stopped_comp_laplacian_nonneg_on_compact hX hF hd ho
    hD (hK n).1 (hK n).2.2 hf hlap (hK n).2.1 (hτ.isStoppingTime n)
  filter_upwards [hcV] with ω hω hp t
  exact stoppedProcess_mem_closedRegion_of_pos hω (hK n).1.isClosed hp t

theorem submartingale_comp_laplacian_nonneg_on_open_of_isotropic_of_integrable_envelope
    {ι Ω : Type*} [Fintype ι] {mΩ : MeasurableSpace Ω}
    {P : Measure Ω} [IsProbabilityMeasure P] {F : Filtration ℝ≥0 mΩ}
    {X : ι → ℝ≥0 → Ω → ℝ} {A : ℝ≥0 → Ω → ℝ} {f : EuclideanSpace ℝ ι → ℝ}
    (hX : ∀ i, IsContinuousLocalMartingale (X i) F P) (hF : F.IsUsual P)
    (hd : ∀ i, Indistinguishable
      (((hX i).isSemimartingale hF).continuousQuadraticVariation hF) A P)
    (ho : ∀ i j, i ≠ j → Indistinguishable
      (((hX i).isSemimartingale hF).continuousQuadraticCovariation
        ((hX j).isSemimartingale hF) hF) 0 P)
    {D : Set (EuclideanSpace ℝ ι)} (hD : IsOpen D) (hf : ContDiffOn ℝ 2 f D)
    (hlap : ∀ x ∈ D, 0 ≤ Laplacian.laplacian f x)
    (hstay : ∀ᵐ ω ∂P, ∀ t, toLp 2 (fun i ↦ X i t ω) ∈ D)
    (hdom : ∀ T : ℝ≥0, ∃ R : Ω → ℝ, Integrable R P ∧
      ∀ᵐ ω ∂P, ∀ t ≤ T, ‖f (toLp 2 (fun i ↦ X i t ω))‖ ≤ R ω) :
    Submartingale (fun t ω ↦ f (toLp 2 (fun i ↦ X i t ω))) F P := by
  have hL := locally_submartingale_comp_laplacian_nonneg_on_open_of_isotropic
    hX hF hd ho hD hf hlap hstay
  obtain ⟨τ, hτ, hY⟩ := hL
  exact submartingale_of_locally_submartingale_of_integrable_envelope
    (hτ.toIsPreLocalizingSequence.adapted_of_masked hF
      (fun n ↦ (hY n).stronglyAdapted.adapted)) ⟨τ, hτ, hY⟩ hdom

end ProbabilityTheory
