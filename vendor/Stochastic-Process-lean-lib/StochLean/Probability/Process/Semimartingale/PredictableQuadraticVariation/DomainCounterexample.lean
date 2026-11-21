/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.LocalMartingale.GeometricLocalMomentCounterexample
public import StochLean.Probability.Process.FiniteVariation.BeforeFieldMoment
public import StochLean.Probability.Process.FiniteVariation.LocallyIntegrableAlgebra
public import StochLean.Probability.Process.FiniteVariation.PredictableLocallyIntegrable
public import StochLean.Probability.Process.FiniteVariation.SingleJump
public import StochLean.Probability.Process.Semimartingale.FiniteVariation
public import StochLean.Probability.Process.Semimartingale.PredictableQuadraticVariation
public import StochLean.Probability.Process.Semimartingale.QuadraticVariation.FiniteVariation
public import StochLean.Probability.Process.Semimartingale.QuadraticCovariation.EnvironmentInvariance
public import StochLean.Probability.Process.Stopping.PredictableAfterCoefficient
public import StochLean.Probability.Process.Path.LifetimeStepJump

/-! # A filtration change can destroy the actual angular domain

The original geometric model and probability measure are unchanged. Its
centered jump at one is a UI martingale in the reveal filtration and a
finite-variation semimartingale in the full-information filtration.

The actual raw quadratic variation is the same squared-jump step in both
environments. In the full-information filtration it is predictable FV, so
the existing theorem constructs its native locally integrable variation and
its actual angle equals that raw quadratic variation. In the smaller reveal
filtration, any proposed native local-integrable-variation witness would make
the increment at one integrable, contradicting the actual infinite second
moment. No candidate angle or angular-domain proof is a premise.

The raw initial square is not subtracted by convention. It vanishes here
because the actual centered step starts at zero.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal

namespace StochLean.GeometricMomentModel

/-- All information about the existing geometric sample is available at zero. -/
def fullInformationFiltration : Filtration ℝ≥0 (inferInstance : MeasurableSpace ℕ) :=
  Filtration.const ℝ≥0 (inferInstance : MeasurableSpace ℕ) le_rfl

private theorem fullInformation_usual : fullInformationFiltration.IsUsual sampleMeasure := by
  refine ⟨⟨?_⟩, ?_⟩
  · intro t
    rw [Filtration.rightCont_eq]
    change _ ≤ (⊤ : MeasurableSpace ℕ)
    exact le_top
  · intro s _
    exact @MeasurableSet.of_discrete ℕ inferInstance inferInstance s

private theorem jumpMartingale_integrableVariation :
    HasIntegrableVariation jumpMartingale sampleMeasure := by
  have h := hasIntegrableVariation_indicator_lifetime_le
    (τ := fun _ : ℕ ↦ ((1 : ℝ≥0) : WithTop ℝ≥0)) measurable_const
    (integrable_value.sub (integrable_const (3 / 2 : ℝ)))
  change HasIntegrableVariation (fun (t : ℝ≥0) (n : ℕ) ↦
    {k : ℕ | ((1 : ℝ≥0) : WithTop ℝ≥0) ≤ (t : WithTop ℝ≥0)}.indicator
      (value - fun _ ↦ 3 / 2) n) sampleMeasure at h
  change HasIntegrableVariation
    (fun (t : ℝ≥0) n ↦ if 1 ≤ t then value n - 3 / 2 else 0) sampleMeasure
  simpa only [indicator_apply, mem_ofPred_eq, WithTop.coe_le_coe, Pi.sub_apply] using h

/-- The same actual source is a semimartingale in two nested usual filtrations.
The full-information assertion is derived from FV, not from a martingale claim. -/
theorem fullInformationFiltration_properties :
    revealFiltration ≤ fullInformationFiltration ∧
      fullInformationFiltration.IsUsual sampleMeasure ∧
      IsSemimartingale jumpMartingale fullInformationFiltration sampleMeasure := by
  refine ⟨fun t ↦ le_top, fullInformation_usual, ?_⟩
  exact jumpMartingale_integrableVariation.hasFiniteVariationPaths.isSemimartingale
    (fun t ↦ show Measurable (jumpMartingale t) from .of_discrete)
    fullInformation_usual (ae_of_all _ jumpMartingale_isCadlagPath)

private theorem raw_quadraticVariation_eq_geometric_square_step
    {F : Filtration ℝ≥0 (inferInstance : MeasurableSpace ℕ)}
    (hF : F.IsUsual sampleMeasure) (hM : IsSemimartingale jumpMartingale F sampleMeasure) :
    Indistinguishable (hM.quadraticVariation hF)
      (fun t n ↦ if (1 : ℝ≥0) ≤ t then (value n - 3 / 2) ^ 2 else 0) sampleMeasure := by
  filter_upwards [hM.quadraticVariation_of_finiteVariation hF
    jumpMartingale_integrableVariation.hasFiniteVariationPaths] with n hn t
  have h0 : jumpMartingale 0 n = 0 := by norm_num [jumpMartingale]
  rw [hn t, h0, zero_pow (by decide : (2 : ℕ) ≠ 0), zero_add]
  have hj (s : ℝ≥0) : jumpProcess jumpMartingale s n =
      if (1 : ℝ≥0) = s then value n - 3 / 2 else 0 :=
    jumpProcess_step_Ici (1 : ℝ≥0) (fun k ↦ value k - 3 / 2) s n
  by_cases ht : (1 : ℝ≥0) ≤ t
  · rw [if_pos ht]
    have h1 : (1 : ℝ≥0) ∈ Ioc 0 t := ⟨by norm_num, ht⟩
    calc
      (∑' s : Ioc 0 t, (jumpProcess jumpMartingale s n) ^ 2) =
          (jumpProcess jumpMartingale 1 n) ^ 2 := by
        apply tsum_eq_single (⟨1, h1⟩ : Ioc 0 t)
        intro s hs
        have hs1 : (s : ℝ≥0) ≠ 1 := fun he ↦ hs (Subtype.ext he)
        simp only [hj, if_neg hs1.symm, zero_pow (by decide : (2 : ℕ) ≠ 0)]
      _ = (value n - 3 / 2) ^ 2 := by rw [hj, if_pos rfl]
  · rw [if_neg ht]
    calc
      (∑' s : Ioc 0 t, (jumpProcess jumpMartingale s n) ^ 2) =
          ∑' _s : Ioc 0 t, (0 : ℝ) := by
        apply tsum_congr
        intro s
        have hs1 : (1 : ℝ≥0) ≠ s := fun he ↦ ht (he.symm ▸ s.property.2)
        simp only [hj, if_neg hs1, zero_pow (by decide : (2 : ℕ) ≠ 0)]
      _ = 0 := tsum_zero

private theorem fullInformation_before_one :
    (isStoppingTime_const fullInformationFiltration (1 : ℝ≥0)).measurableSpaceBefore =
      (inferInstance : MeasurableSpace ℕ) := by
  rw [IsStoppingTime.measurableSpaceBefore_const]
  apply le_antisymm le_top
  exact le_sup_left

private theorem geometric_square_step_predictable :
    IsStronglyPredictable fullInformationFiltration
      (fun t n ↦ if (1 : ℝ≥0) ≤ t then (value n - 3 / 2) ^ 2 else 0) := by
  have hτ := isPredictableStoppingTime_const fullInformationFiltration sampleMeasure (1 : ℝ≥0)
  have hf : StronglyMeasurable[hτ.1.measurableSpaceBefore]
      (fun n : ℕ ↦ (value n - 3 / 2) ^ 2) := by
    rw [fullInformation_before_one]
    exact .of_discrete
  have hp := hf.isStronglyPredictable_indicator_stoppingTime_le
    hτ fullInformation_usual.complete_initial
  change IsStronglyPredictable fullInformationFiltration (fun (t : ℝ≥0) (n : ℕ) ↦
    {k : ℕ | ((1 : ℝ≥0) : WithTop ℝ≥0) ≤ (t : WithTop ℝ≥0)}.indicator
      (fun k : ℕ ↦ (value k - 3 / 2) ^ 2) n) at hp
  simpa only [indicator_apply, mem_ofPred_eq, WithTop.coe_le_coe] using hp

private theorem geometric_square_step_finiteVariation :
    HasFiniteVariationPaths
      (fun t n ↦ if (1 : ℝ≥0) ≤ t then (value n - 3 / 2) ^ 2 else 0) sampleMeasure := by
  apply ae_of_all
  intro n
  have hm : Monotone (fun t : ℝ≥0 ↦ if 1 ≤ t then (value n - 3 / 2) ^ 2 else 0) := by
    intro s t hst
    by_cases hs : (1 : ℝ≥0) ≤ s
    · simp only [if_pos hs, if_pos (hs.trans hst), le_refl]
    · simp only [if_neg hs]
      split_ifs <;> first | exact sq_nonneg _ | exact le_rfl
  exact (hm.monotoneOn univ).locallyBoundedVariationOn

private theorem geometric_reveal_before_zero_one (s : Set ℕ)
    (hs : MeasurableSet[(isStoppingTime_const revealFiltration
      (1 : ℝ≥0)).measurableSpaceBefore] s) :
    sampleMeasure s = 0 ∨ sampleMeasure s = 1 := by
  have he : (isStoppingTime_const revealFiltration (1 : ℝ≥0)).measurableSpaceBefore = ⊥ := by
    rw [IsStoppingTime.measurableSpaceBefore_const]
    apply bot_unique
    refine sup_le ?_ (iSup_le fun t ↦ iSup_le fun ht ↦ ?_)
    · change (if (1 : ℝ≥0) ≤ 0 then ⊤ else ⊥) ≤ ⊥
      norm_num
    · change (if 1 ≤ t then ⊤ else ⊥) ≤ ⊥
      simp only [if_neg (not_le.mpr ht), le_refl]
  rw [he] at hs
  rcases MeasurableSpace.measurableSet_bot_iff.mp hs with rfl | rfl
  · exact Or.inl measure_empty
  · exact Or.inr measure_univ

/-- The actual angular domain exists with full initial information but fails
after passing to the smaller usual reveal filtration, although the process
remains a genuine semimartingale and its actual raw quadratic variation is unchanged. -/
theorem actual_angular_domain_lost_under_smaller_filtration :
    let hSF := jumpMartingale_isLocalMartingale.isSemimartingale revealFiltration_isUsual
    let hSG := fullInformationFiltration_properties.2.2
    Indistinguishable (hSF.quadraticVariation revealFiltration_isUsual)
      (hSG.quadraticVariation fullInformationFiltration_properties.2.1) sampleMeasure ∧
    Indistinguishable (hSG.quadraticVariation fullInformationFiltration_properties.2.1)
      (fun t n ↦ if (1 : ℝ≥0) ≤ t then (value n - 3 / 2) ^ 2 else 0) sampleMeasure ∧
    ¬ HasLocallyIntegrableVariation (hSF.quadraticVariation revealFiltration_isUsual)
      revealFiltration sampleMeasure ∧
    ∃ hQG : HasLocallyIntegrableVariation
        (hSG.quadraticVariation fullInformationFiltration_properties.2.1)
          fullInformationFiltration sampleMeasure,
      Indistinguishable
        (hSG.predictableQuadraticVariation fullInformationFiltration_properties.2.1 hQG)
        (hSG.quadraticVariation fullInformationFiltration_properties.2.1) sampleMeasure := by
  intro hSF hSG
  have hrawF := raw_quadraticVariation_eq_geometric_square_step revealFiltration_isUsual hSF
  have hraw := hSF.quadraticVariation_congr_filtration hSG
    revealFiltration_isUsual fullInformationFiltration_properties.2.1
  have hrawG := hraw.symm.trans hrawF
  refine ⟨hraw, hrawG, ?_, ?_⟩
  · intro hQF
    have hi := hQF.integrable_sub_at_of_before_zero_one (T := 1) (by norm_num)
      geometric_reveal_before_zero_one
      (show AEStronglyMeasurable _ sampleMeasure from
        (show StronglyMeasurable _ from .of_discrete).aestronglyMeasurable)
    have hiSquare : Integrable (fun n ↦ (value n - 3 / 2) ^ 2) sampleMeasure := by
      apply hi.congr
      filter_upwards [hrawF] with n hn
      rw [hn 1, hn 0]
      norm_num
    have hcenter : MemLp (fun n ↦ value n - 3 / 2) 2 sampleMeasure :=
      (memLp_two_iff_integrable_sq
        (show AEStronglyMeasurable _ sampleMeasure from
          (show StronglyMeasurable _ from .of_discrete).aestronglyMeasurable)).mpr hiSquare
    have hc : MemLp (fun _ : ℕ ↦ (3 / 2 : ℝ)) 2 sampleMeasure := memLp_const _
    apply not_memLp_two
    convert! hcenter.add hc using 1
    ext n
    simp only [Pi.add_apply, sub_add_cancel]
  · have hcN : HasCadlagPaths
        (fun t n ↦ if (1 : ℝ≥0) ≤ t then (value n - 3 / 2) ^ 2 else 0) sampleMeasure :=
      ae_of_all _ fun n ↦ isCadlagPath_step_Ici 1 ((value n - 3 / 2) ^ 2)
    have hLN := geometric_square_step_predictable.hasLocallyIntegrableVariation
      fullInformationFiltration_properties.2.1 hcN geometric_square_step_finiteVariation
    have hQG : HasLocallyIntegrableVariation
        (hSG.quadraticVariation fullInformationFiltration_properties.2.1)
          fullInformationFiltration sampleMeasure := hLN.congr hrawG.symm
    have hzero := (isContinuousLocalMartingale_const_initial
      (F := fullInformationFiltration) (P := sampleMeasure)
      (Z := fun _ : ℕ ↦ (0 : ℝ)) measurable_const).1
    have hres : IsLocalMartingale
        (hSG.quadraticVariation fullInformationFiltration_properties.2.1 -
          (fun t n ↦ if (1 : ℝ≥0) ≤ t then (value n - 3 / 2) ^ 2 else 0))
        fullInformationFiltration sampleMeasure := by
      apply hzero.congr fullInformationFiltration_properties.2.1
        ((hSG.adapted_quadraticVariation fullInformationFiltration_properties.2.1).sub
          geometric_square_step_predictable.stronglyAdapted.adapted)
      filter_upwards [hrawG] with n hn t
      change 0 = hSG.quadraticVariation fullInformationFiltration_properties.2.1 t n - _
      rw [hn t, sub_self]
    have hangle := hSG.predictableQuadraticVariation_unique
      fullInformationFiltration_properties.2.1 hQG geometric_square_step_predictable
      geometric_square_step_finiteVariation
      (ae_of_all _ fun n ↦ by norm_num) hres
    exact ⟨hQG, hangle.trans hrawG.symm⟩

end StochLean.GeometricMomentModel
