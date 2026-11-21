/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.Semimartingale.PredictableQuadraticVariation.ThreePointModel
public import StochLean.Probability.Process.Semimartingale.PredictableQuadraticVariation
public import StochLean.Probability.Process.Semimartingale.QuadraticVariation.FiniteVariation
public import StochLean.Probability.Process.FiniteVariation.SingleJump
public import StochLean.Probability.Process.Stopping.PredictableAfterCoefficient
public import StochLean.Probability.Process.Path.LifetimeStepJump

/-! # Actual predictable quadratic variation changes with an equivalent law

The preceding three-point model fixes the sample space, filtration, and bounded
UI/L2 martingale. Its actual raw quadratic variation is the same squared jump
under both equivalent probability laws. Its actual predictable quadratic
variations, selected by the existing domain-guarded owner, differ.

The domains are proved from actual single-step integrable variation. The
angle identities follow by full compensator uniqueness after constructing
the centered squared-jump UI martingales. No angular process, compensator,
domain proof, or martingale certificate is an input to the counterexample.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal

namespace StochLean.SemimartingaleRegression.ThreePoint

private theorem step_integrableVariation (μ : Measure (Fin 3)) [IsFiniteMeasure μ]
    (f : Fin 3 → ℝ) :
    HasIntegrableVariation (fun (t : ℝ≥0) i ↦ if 1 ≤ t then f i else 0) μ := by
  have h := hasIntegrableVariation_indicator_lifetime_le
    (τ := fun _ : Fin 3 ↦ ((1 : ℝ≥0) : WithTop ℝ≥0))
    measurable_const (show Integrable f μ from Integrable.of_finite)
  change HasIntegrableVariation (fun (t : ℝ≥0) (i : Fin 3) ↦
    {j : Fin 3 | ((1 : ℝ≥0) : WithTop ℝ≥0) ≤ (t : WithTop ℝ≥0)}.indicator f i) μ at h
  simpa only [indicator_apply, mem_ofPred_eq, WithTop.coe_le_coe] using h

private theorem raw_quadraticVariation_eq_square_step
    {μ : Measure (Fin 3)} [IsProbabilityMeasure μ] (hF : revealFiltration.IsUsual μ)
    (hM : IsSemimartingale jumpMartingale revealFiltration μ) :
    Indistinguishable (hM.quadraticVariation hF)
      (fun t i ↦ if (1 : ℝ≥0) ≤ t then (jumpSize i) ^ 2 else 0) μ := by
  have hv : HasFiniteVariationPaths jumpMartingale μ :=
    (step_integrableVariation μ jumpSize).hasFiniteVariationPaths
  filter_upwards [hM.quadraticVariation_of_finiteVariation hF hv] with i hi t
  have h0 : jumpMartingale 0 i = 0 := by norm_num [jumpMartingale]
  rw [hi t, h0, zero_pow (by decide : (2 : ℕ) ≠ 0), zero_add]
  have hj (s : ℝ≥0) : jumpProcess jumpMartingale s i =
      if (1 : ℝ≥0) = s then jumpSize i else 0 :=
    jumpProcess_step_Ici (1 : ℝ≥0) jumpSize s i
  by_cases ht : (1 : ℝ≥0) ≤ t
  · rw [if_pos ht]
    have h1 : (1 : ℝ≥0) ∈ Ioc 0 t := ⟨by norm_num, ht⟩
    calc
      (∑' s : Ioc 0 t, (jumpProcess jumpMartingale s i) ^ 2) =
          (jumpProcess jumpMartingale 1 i) ^ 2 := by
        apply tsum_eq_single (⟨1, h1⟩ : Ioc 0 t)
        intro s hs
        have hs1 : (s : ℝ≥0) ≠ 1 := fun he ↦ hs (Subtype.ext he)
        simp only [hj, if_neg hs1.symm, zero_pow (by decide : (2 : ℕ) ≠ 0)]
      _ = (jumpSize i) ^ 2 := by rw [hj, if_pos rfl]
  · rw [if_neg ht]
    calc
      (∑' s : Ioc 0 t, (jumpProcess jumpMartingale s i) ^ 2) =
          ∑' _s : Ioc 0 t, (0 : ℝ) := by
        apply tsum_congr
        intro s
        have hs1 : (1 : ℝ≥0) ≠ s := fun he ↦ ht (he.symm ▸ s.property.2)
        simp only [hj, if_neg hs1, zero_pow (by decide : (2 : ℕ) ≠ 0)]
      _ = 0 := tsum_zero

private theorem actual_angle_for_law
    {μ : Measure (Fin 3)} [IsProbabilityMeasure μ] (hF : revealFiltration.IsUsual μ)
    (hM : IsSemimartingale jumpMartingale revealFiltration μ) {v : ℝ}
    (hv : (∫ i, (jumpSize i) ^ 2 ∂μ) = v) :
    ∃ hQ : HasLocallyIntegrableVariation (hM.quadraticVariation hF) revealFiltration μ,
      Indistinguishable (hM.quadraticVariation hF)
        (fun t i ↦ if (1 : ℝ≥0) ≤ t then (jumpSize i) ^ 2 else 0) μ ∧
      Indistinguishable (hM.predictableQuadraticVariation hF hQ)
        (fun t _ ↦ if (1 : ℝ≥0) ≤ t then v else 0) μ := by
  have heQ := raw_quadraticVariation_eq_square_step hF hM
  have hiQ : HasIntegrableVariation (hM.quadraticVariation hF) μ :=
    (step_integrableVariation μ (fun i ↦ (jumpSize i) ^ 2)).congr heQ.symm
  have hvQ : HasLocallyIntegrableVariation (hM.quadraticVariation hF) revealFiltration μ :=
    hiQ.hasLocallyIntegrableVariation
  let B : ℝ≥0 → Fin 3 → ℝ := fun t _ ↦ if 1 ≤ t then v else 0
  have hpB : IsStronglyPredictable revealFiltration B := by
    have hτ := isPredictableStoppingTime_const revealFiltration μ (1 : ℝ≥0)
    have hf : StronglyMeasurable[hτ.1.measurableSpaceBefore] (fun _ : Fin 3 ↦ v) :=
      stronglyMeasurable_const
    have hp := hf.isStronglyPredictable_indicator_stoppingTime_le hτ hF.complete_initial
    change IsStronglyPredictable revealFiltration (fun (t : ℝ≥0) (i : Fin 3) ↦
      {j : Fin 3 | ((1 : ℝ≥0) : WithTop ℝ≥0) ≤ (t : WithTop ℝ≥0)}.indicator
        (fun _ : Fin 3 ↦ v) i) at hp
    simpa only [B, indicator_apply, mem_ofPred_eq, WithTop.coe_le_coe] using hp
  have hvB : HasFiniteVariationPaths B μ :=
    (step_integrableVariation μ (fun _ ↦ v)).hasFiniteVariationPaths
  have hB0 : B 0 =ᵐ[μ] 0 := Eventually.of_forall fun i ↦ by norm_num [B]
  have hmean : (∫ i, (jumpSize i) ^ 2 - v ∂μ) = 0 := by
    rw [integral_sub Integrable.of_finite (integrable_const v), hv]
    simp
  have hu := isUIMartingale_step_of_integral_eq_zero μ
    (fun i ↦ (jumpSize i) ^ 2 - v) hmean
  have hc : HasCadlagPaths
      (fun (t : ℝ≥0) i ↦ if 1 ≤ t then (jumpSize i) ^ 2 - v else 0) μ :=
    Eventually.of_forall fun i ↦ isCadlagPath_step_Ici 1 ((jumpSize i) ^ 2 - v)
  have hres : IsLocalMartingale (hM.quadraticVariation hF - B) revealFiltration μ := by
    apply (hu.isLocalMartingale hc).congr hF
      ((hM.adapted_quadraticVariation hF).sub hpB.stronglyAdapted.adapted)
    filter_upwards [heQ] with i hi t
    change (if (1 : ℝ≥0) ≤ t then (jumpSize i) ^ 2 - v else 0) =
      hM.quadraticVariation hF t i - (if (1 : ℝ≥0) ≤ t then v else 0)
    rw [hi t]
    split_ifs <;> ring
  exact ⟨hvQ, heQ, hM.predictableQuadraticVariation_unique hF hvQ hpB hvB hB0 hres⟩

/-- The same actual raw bracket has two different actual selected angles.
All existence-domain proofs are constructed here from the finite model. -/
theorem actual_angles_of_equivalent_measures :
    let hMP := jumpMartingale_ui_and_squareIntegrable.2.1.isLocalMartingale
      (Eventually.of_forall fun i ↦ isCadlagPath_step_Ici 1 (jumpSize i))
    let hMQ := jumpMartingale_ui_and_squareIntegrable.2.2.2.1.isLocalMartingale
      (Eventually.of_forall fun i ↦ isCadlagPath_step_Ici 1 (jumpSize i))
    let hSP := hMP.isSemimartingale revealFiltration_isUsual.1
    let hSQ := hMQ.isSemimartingale revealFiltration_isUsual.2
    ∃ hQP : HasLocallyIntegrableVariation
        (hSP.quadraticVariation revealFiltration_isUsual.1) revealFiltration measureP,
      ∃ hQQ : HasLocallyIntegrableVariation
        (hSQ.quadraticVariation revealFiltration_isUsual.2) revealFiltration measureQ,
        Indistinguishable (hSP.quadraticVariation revealFiltration_isUsual.1)
          (fun t i ↦ if (1 : ℝ≥0) ≤ t then (jumpSize i) ^ 2 else 0) measureP ∧
        Indistinguishable (hSQ.quadraticVariation revealFiltration_isUsual.2)
          (fun t i ↦ if (1 : ℝ≥0) ≤ t then (jumpSize i) ^ 2 else 0) measureQ ∧
        Indistinguishable (hSP.predictableQuadraticVariation revealFiltration_isUsual.1 hQP)
          (fun t _ ↦ if (1 : ℝ≥0) ≤ t then (1 / 2 : ℝ) else 0) measureP ∧
        Indistinguishable (hSQ.predictableQuadraticVariation revealFiltration_isUsual.2 hQQ)
          (fun t _ ↦ if (1 : ℝ≥0) ≤ t then (1 / 4 : ℝ) else 0) measureQ := by
  intro hMP hMQ hSP hSQ
  obtain ⟨hQP, heQP, heAP⟩ :=
    actual_angle_for_law revealFiltration_isUsual.1 hSP jumpSize_moments.2.2.1
  obtain ⟨hQQ, heQQ, heAQ⟩ :=
    actual_angle_for_law revealFiltration_isUsual.2 hSQ jumpSize_moments.2.2.2
  exact ⟨hQP, hQQ, heQP, heQQ, heAP, heAQ⟩

/-- Equivalence of probability laws does not make the actual predictable
quadratic variation invariant, even for the same bounded UI/L2 martingale. -/
theorem actual_angles_not_indistinguishable :
    let hMP := jumpMartingale_ui_and_squareIntegrable.2.1.isLocalMartingale
      (Eventually.of_forall fun i ↦ isCadlagPath_step_Ici 1 (jumpSize i))
    let hMQ := jumpMartingale_ui_and_squareIntegrable.2.2.2.1.isLocalMartingale
      (Eventually.of_forall fun i ↦ isCadlagPath_step_Ici 1 (jumpSize i))
    let hSP := hMP.isSemimartingale revealFiltration_isUsual.1
    let hSQ := hMQ.isSemimartingale revealFiltration_isUsual.2
    ∃ hQP : HasLocallyIntegrableVariation
        (hSP.quadraticVariation revealFiltration_isUsual.1) revealFiltration measureP,
      ∃ hQQ : HasLocallyIntegrableVariation
        (hSQ.quadraticVariation revealFiltration_isUsual.2) revealFiltration measureQ,
        ¬ Indistinguishable
          (hSP.predictableQuadraticVariation revealFiltration_isUsual.1 hQP)
          (hSQ.predictableQuadraticVariation revealFiltration_isUsual.2 hQQ) measureP ∧
        ¬ Indistinguishable
          (hSP.predictableQuadraticVariation revealFiltration_isUsual.1 hQP)
          (hSQ.predictableQuadraticVariation revealFiltration_isUsual.2 hQQ) measureQ := by
  intro hMP hMQ hSP hSQ
  obtain ⟨hQP, hQQ, _, _, hp, hq⟩ := actual_angles_of_equivalent_measures
  have hqP := measures_mutuallyAbsolutelyContinuous.1.ae_le hq
  have hpQ := measures_mutuallyAbsolutelyContinuous.2.ae_le hp
  refine ⟨hQP, hQQ, ?_, ?_⟩
  · intro he
    have hf : ∀ᵐ i ∂measureP, False := by
      filter_upwards [hp, hqP, he] with i hpi hqi hei
      have h := hei 1
      rw [hpi 1, hqi 1] at h
      norm_num at h
    exact (NeZero.ne measureP) (by simpa using hf)
  · intro he
    have hf : ∀ᵐ i ∂measureQ, False := by
      filter_upwards [hpQ, hq, he] with i hpi hqi hei
      have h := hei 1
      rw [hpi 1, hqi 1] at h
      norm_num at h
    exact (NeZero.ne measureQ) (by simpa using hf)

end StochLean.SemimartingaleRegression.ThreePoint
