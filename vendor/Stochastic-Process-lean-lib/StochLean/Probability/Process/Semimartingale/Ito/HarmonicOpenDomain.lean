/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.Semimartingale.Ito.HarmonicClosedRegion
public import StochLean.Probability.Process.Stopping.ClosedRegion
public import StochLean.ForMathlib.Topology.OpenDomainExhaustion
public import StochLean.Probability.Process.LocalMartingale.Localization

/-! # Harmonic composition on an arbitrary open Euclidean domain

Compact regions, globally smooth local extensions, and actual first-exit
localizers are constructed, including the zero-stopping initial branch.
The full composition has continuous paths and its local-martingale property
is recovered by the existing masked local-to-local theorem.
-/

@[expose] public section

open MeasureTheory Filter Set StochLean InnerProductSpace WithLp
open scoped NNReal

namespace ProbabilityTheory

theorem isContinuousLocalMartingale_comp_harmonic_on_open_of_isotropic_of_nonempty
    {ι Ω : Type*} [Fintype ι] {mΩ : MeasurableSpace Ω}
    {P : Measure Ω} [IsFiniteMeasure P] {F : Filtration ℝ≥0 mΩ}
    {X : ι → ℝ≥0 → Ω → ℝ} {A : ℝ≥0 → Ω → ℝ} {f : EuclideanSpace ℝ ι → ℝ}
    (hX : ∀ i, IsContinuousLocalMartingale (X i) F P) (hF : F.IsUsual P)
    (hd : ∀ i, Indistinguishable
      (((hX i).isSemimartingale hF).continuousQuadraticVariation hF) A P)
    (ho : ∀ i j, i ≠ j → Indistinguishable
      (((hX i).isSemimartingale hF).continuousQuadraticCovariation
        ((hX j).isSemimartingale hF) hF) 0 P)
    {D : Set (EuclideanSpace ℝ ι)} (hD : IsOpen D) (hDne : D.Nonempty)
    (hf : HarmonicOnNhd f D)
    (hstay : ∀ᵐ ω ∂P, ∀ t, toLp 2 (fun i ↦ X i t ω) ∈ D) :
    IsContinuousLocalMartingale (fun t ω ↦ f (toLp 2 (fun i ↦ X i t ω))) F P := by
  classical
  obtain ⟨c, hc⟩ := hDne
  obtain ⟨K, hK, hKm, hKcover⟩ := exists_compact_exhaustion_with_basepoint hD hc
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
  have hcomp : HasContinuousPaths (fun t ω ↦ f (V t ω)) P := by
    filter_upwards [hcV, hstay] with ω hω hDω
    exact continuousOn_univ.mp (hf.continuousOn.comp hω.continuousOn (fun t _ ↦ hDω t))
  refine ⟨isLocalMartingale_of_locally_localMartingale hF hcomp.hasCadlagPaths ?_, hcomp⟩
  refine ⟨τ, hτ, fun n ↦ ?_⟩
  apply (isContinuousLocalMartingale_masked_stopped_comp_harmonic_on_closed hX hF hd ho
    hD (hK n).1.isClosed (hK n).2.2 hf (hK n).2.1 (hτ.isStoppingTime n) ?_).1
  filter_upwards [hcV] with ω hω hp t
  exact stoppedProcess_mem_closedRegion_of_pos hω (hK n).1.isClosed hp t

theorem isContinuousLocalMartingale_comp_harmonic_on_open_of_isotropic
    {ι Ω : Type*} [Fintype ι] {mΩ : MeasurableSpace Ω}
    {P : Measure Ω} [IsProbabilityMeasure P] {F : Filtration ℝ≥0 mΩ}
    {X : ι → ℝ≥0 → Ω → ℝ} {A : ℝ≥0 → Ω → ℝ} {f : EuclideanSpace ℝ ι → ℝ}
    (hX : ∀ i, IsContinuousLocalMartingale (X i) F P) (hF : F.IsUsual P)
    (hd : ∀ i, Indistinguishable
      (((hX i).isSemimartingale hF).continuousQuadraticVariation hF) A P)
    (ho : ∀ i j, i ≠ j → Indistinguishable
      (((hX i).isSemimartingale hF).continuousQuadraticCovariation
        ((hX j).isSemimartingale hF) hF) 0 P)
    {D : Set (EuclideanSpace ℝ ι)} (hD : IsOpen D) (hf : HarmonicOnNhd f D)
    (hstay : ∀ᵐ ω ∂P, ∀ t, toLp 2 (fun i ↦ X i t ω) ∈ D) :
    IsContinuousLocalMartingale (fun t ω ↦ f (toLp 2 (fun i ↦ X i t ω))) F P := by
  obtain ⟨ω, hω⟩ := hstay.exists
  exact isContinuousLocalMartingale_comp_harmonic_on_open_of_isotropic_of_nonempty
    hX hF hd ho hD ⟨_, hω 0⟩ hf hstay

end ProbabilityTheory
