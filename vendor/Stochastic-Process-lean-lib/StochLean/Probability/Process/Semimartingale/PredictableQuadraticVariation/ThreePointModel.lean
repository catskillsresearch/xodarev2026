/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Martingale.Doob.CenteredSingleJump
public import StochLean.Probability.Process.Filtration.Usual
public import StochLean.Probability.Process.Path.RightStep
public import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure

/-! # A three-point martingale with two equivalent probability laws

At time one the filtration reveals a random variable taking values -1, 0, 1.
Both explicitly constructed laws are symmetric, but their variances differ.
All three atoms have positive mass under each law, so the trivial initial
sigma-field is genuinely complete. No augmentation or path modification is
silently imposed. The process is bounded, UI, and square-integrable under
both laws.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal

namespace StochLean.SemimartingaleRegression.ThreePoint

/-- The three possible values, indexed in increasing order. -/
def jumpSize (i : Fin 3) : ℝ := (i.val : ℝ) - 1

/-- Masses 1/4, 1/2, 1/4 at -1, 0, 1. -/
noncomputable def measureP : Measure (Fin 3) :=
  (1 / 4 : ℝ≥0∞) • Measure.dirac 0 + (1 / 2 : ℝ≥0∞) • Measure.dirac 1 +
    (1 / 4 : ℝ≥0∞) • Measure.dirac 2

/-- Masses 1/8, 3/4, 1/8 at -1, 0, 1. -/
noncomputable def measureQ : Measure (Fin 3) :=
  (1 / 8 : ℝ≥0∞) • Measure.dirac 0 + (3 / 4 : ℝ≥0∞) • Measure.dirac 1 +
    (1 / 8 : ℝ≥0∞) • Measure.dirac 2

instance instIsProbabilityMeasureMeasureP : IsProbabilityMeasure measureP := by
  constructor
  apply (ENNReal.toReal_eq_one_iff _).mp
  norm_num [measureP, ENNReal.toReal_add]

instance instIsProbabilityMeasureMeasureQ : IsProbabilityMeasure measureQ := by
  constructor
  apply (ENNReal.toReal_eq_one_iff _).mp
  have h34 : (3 / 4 : ℝ≥0∞) ≠ ∞ := ENNReal.div_ne_top (by norm_num) (by norm_num)
  norm_num [measureQ, ENNReal.toReal_add, h34]

/-- No information is known before one; the whole sample is known at one. -/
noncomputable def revealFiltration :
    Filtration ℝ≥0 (inferInstance : MeasurableSpace (Fin 3)) where
  seq t := if 1 ≤ t then ⊤ else ⊥
  mono' := by
    intro s t hst
    by_cases hs : (1 : ℝ≥0) ≤ s
    · simp only [if_pos hs, if_pos (hs.trans hst), le_refl]
    · simp only [if_neg hs]
      exact bot_le
  le' _ := le_top

/-- The actual mean-zero jump occurs at the deterministic time one. -/
noncomputable def jumpMartingale (t : ℝ≥0) (i : Fin 3) : ℝ :=
  if 1 ≤ t then jumpSize i else 0

private theorem singleton_measureP_ne_zero (i : Fin 3) : measureP {i} ≠ 0 := by
  fin_cases i <;> norm_num [measureP, Pi.single_apply, Fin.ext_iff]

private theorem singleton_measureQ_ne_zero (i : Fin 3) : measureQ {i} ≠ 0 := by
  fin_cases i <;> norm_num [measureQ, Pi.single_apply, Fin.ext_iff]

private theorem null_set_eq_empty {μ : Measure (Fin 3)}
    (hμ : ∀ i, μ {i} ≠ 0) {s : Set (Fin 3)} (hs : μ s = 0) : s = ∅ := by
  apply eq_empty_iff_forall_notMem.mpr
  intro i hi
  exact hμ i (measure_mono_null (singleton_subset_iff.mpr hi) hs)

/-- The two actual laws have exactly the same null sets. -/
theorem measures_mutuallyAbsolutelyContinuous : measureP ≪ measureQ ∧ measureQ ≪ measureP := by
  constructor
  · intro s hs
    rw [null_set_eq_empty singleton_measureQ_ne_zero hs]
    exact measure_empty
  · intro s hs
    rw [null_set_eq_empty singleton_measureP_ne_zero hs]
    exact measure_empty

private theorem reveal_rightContinuous : revealFiltration.IsRightContinuous := by
  constructor
  intro t
  rw [Filtration.rightCont_eq]
  by_cases ht : (1 : ℝ≥0) ≤ t
  · change _ ≤ if 1 ≤ t then ⊤ else ⊥
    rw [if_pos ht]
    exact le_top
  · obtain ⟨u, htu, hu⟩ := exists_between (lt_of_not_ge ht)
    apply iInf₂_le_of_le u htu
    change (if 1 ≤ u then ⊤ else ⊥) ≤ if 1 ≤ t then ⊤ else ⊥
    simp only [if_neg (not_le.mpr hu), if_neg ht, le_refl]

private theorem reveal_usual_of_positive_atoms {μ : Measure (Fin 3)}
    (hμ : ∀ i, μ {i} ≠ 0) : revealFiltration.IsUsual μ := by
  refine ⟨reveal_rightContinuous, ?_⟩
  intro s hs
  rw [null_set_eq_empty hμ hs]
  exact @MeasurableSet.empty _ (revealFiltration ⊥)

/-- The specified unaugmented filtration satisfies both usual conditions
for each of the two positive-atom probability laws. -/
theorem revealFiltration_isUsual :
    revealFiltration.IsUsual measureP ∧ revealFiltration.IsUsual measureQ :=
  ⟨reveal_usual_of_positive_atoms singleton_measureP_ne_zero,
    reveal_usual_of_positive_atoms singleton_measureQ_ne_zero⟩

/-- Actual first moments agree and actual second moments differ. -/
theorem jumpSize_moments :
    (∫ i, jumpSize i ∂measureP) = 0 ∧ (∫ i, jumpSize i ∂measureQ) = 0 ∧
      (∫ i, (jumpSize i) ^ 2 ∂measureP) = 1 / 2 ∧
      (∫ i, (jumpSize i) ^ 2 ∂measureQ) = 1 / 4 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    rw [integral_fintype Integrable.of_finite, Fin.sum_univ_three] <;>
    norm_num [measureP, measureQ, measureReal_def, jumpSize, Pi.single_apply, Fin.ext_iff]

private theorem reveal_before_one :
    (isStoppingTime_const revealFiltration (1 : ℝ≥0)).measurableSpaceBefore = ⊥ := by
  rw [IsStoppingTime.measurableSpaceBefore_const]
  apply bot_unique
  refine sup_le ?_ (iSup_le fun t ↦ iSup_le fun ht ↦ ?_)
  · change (if (1 : ℝ≥0) ≤ 0 then ⊤ else ⊥) ≤ ⊥
    norm_num
  · change (if 1 ≤ t then ⊤ else ⊥) ≤ ⊥
    simp only [if_neg (not_le.mpr ht), le_refl]

/-- For this actual reveal filtration, every finite-space mean-zero jump
gives a UI martingale. Usualness is not assumed or asserted for arbitrary μ. -/
theorem isUIMartingale_step_of_integral_eq_zero (μ : Measure (Fin 3))
    [IsProbabilityMeasure μ] (f : Fin 3 → ℝ) (hf : (∫ i, f i ∂μ) = 0) :
    IsUIMartingale (fun t : ℝ≥0 ↦ fun i ↦ if 1 ≤ t then f i else 0)
      revealFiltration μ := by
  let hτ := isStoppingTime_const revealFiltration (1 : ℝ≥0)
  have hm : StronglyMeasurable[hτ.measurableSpace] f := by
    rw [IsStoppingTime.measurableSpace_const]
    have h1 : revealFiltration 1 = (inferInstance : MeasurableSpace (Fin 3)) := by
      change (if (1 : ℝ≥0) ≤ 1 then ⊤ else ⊥) = ⊤
      exact if_pos le_rfl
    rw [h1]
    exact (measurable_of_finite f).stronglyMeasurable
  have hz : μ[f | hτ.measurableSpaceBefore] =ᵐ[μ] 0 := by
    rw [reveal_before_one, condExp_bot, hf]
    exact Eventually.of_forall fun _ ↦ rfl
  have hu := isUIMartingale_indicator_stoppingTime_le_of_condExp_before_eq_zero
    hτ hm Integrable.of_finite hz
  change IsUIMartingale (fun (t : ℝ≥0) (i : Fin 3) ↦
    {j : Fin 3 | ((1 : ℝ≥0) : WithTop ℝ≥0) ≤ (t : WithTop ℝ≥0)}.indicator f i)
      revealFiltration μ at hu
  simpa only [indicator_apply, mem_ofPred_eq, WithTop.coe_le_coe] using hu

/-- One common bounded process is a genuine UI and L2 martingale under
both equivalent laws, not merely under one chosen environment. -/
theorem jumpMartingale_ui_and_squareIntegrable :
    (∀ t i, ‖jumpMartingale t i‖ ≤ 1) ∧
      IsUIMartingale jumpMartingale revealFiltration measureP ∧
      IsSquareIntegrableMartingale jumpMartingale revealFiltration measureP ∧
      IsUIMartingale jumpMartingale revealFiltration measureQ ∧
      IsSquareIntegrableMartingale jumpMartingale revealFiltration measureQ := by
  have hp := isUIMartingale_step_of_integral_eq_zero measureP jumpSize jumpSize_moments.1
  have hq := isUIMartingale_step_of_integral_eq_zero measureQ jumpSize jumpSize_moments.2.1
  refine ⟨?_, hp, ⟨hp.1, ?_⟩, hq, ⟨hq.1, ?_⟩⟩
  · intro t i
    by_cases ht : (1 : ℝ≥0) ≤ t
    · fin_cases i <;> norm_num [jumpMartingale, ht, jumpSize]
    · simp only [jumpMartingale, if_neg ht, norm_zero, zero_le_one]
  · intro t
    exact (memLp_two_iff_integrable_sq
      (measurable_of_finite (jumpMartingale t)).aestronglyMeasurable).mpr Integrable.of_finite
  · intro t
    exact (memLp_two_iff_integrable_sq
      (measurable_of_finite (jumpMartingale t)).aestronglyMeasurable).mpr Integrable.of_finite

end StochLean.SemimartingaleRegression.ThreePoint
