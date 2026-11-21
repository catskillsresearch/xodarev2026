/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.LocalMartingale.InitialMagnitudeModel
public import StochLean.Probability.Process.LocalMartingale.BeforeFieldMoment
public import StochLean.Probability.Process.Filtration.MartingaleAugmentation
public import StochLean.Probability.Process.Semimartingale.FiniteVariation
public import Mathlib.Analysis.BoundedVariation

/-! # Shrinking a usual filtration can destroy the local martingale property

Both filtrations live on the genuinely completed symmetric-inverse probability
space. The larger one initially knows the magnitude of the non-integrable
coefficient, and the smaller one has only completed trivial information before
time one. The same closed-step process is a native local martingale in the
larger filtration but not in the smaller one. It remains an adapted cadlag
finite-variation semimartingale in the smaller filtration.

The non-martingale argument uses actual probability-zero-or-one representatives
of completed initial events, not the false assertion that all such events
are null. Native localization and its positive-lifetime masks are retained.
This realizes Protter's second example on printed page 128.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal

namespace StochLean.SymmetricInverseModel

/-- The smaller filtration in the genuinely completed ambient probability space. -/
noncomputable def smallFiltration :
    Filtration ℝ≥0 (inferInstance : MeasurableSpace (NullMeasurableSpace ℝ sampleMeasure)) :=
  rawSmallFiltration.usualAugmentation sampleMeasure

/-- The larger filtration in that same genuinely completed probability space. -/
noncomputable def magnitudeFiltration :
    Filtration ℝ≥0 (inferInstance : MeasurableSpace (NullMeasurableSpace ℝ sampleMeasure)) :=
  rawMagnitudeFiltration.usualAugmentation sampleMeasure

theorem completedFiltrations_usual_and_le :
    smallFiltration.IsUsual sampleMeasure.completion ∧
      magnitudeFiltration.IsUsual sampleMeasure.completion ∧
        smallFiltration ≤ magnitudeFiltration := by
  refine ⟨rawSmallFiltration.usualAugmentation_isUsual sampleMeasure,
    rawMagnitudeFiltration.usualAugmentation_isUsual sampleMeasure, ?_⟩
  rw [smallFiltration, magnitudeFiltration,
    Filtration.usualAugmentation_eq_withNullSets rawFiltrations_rightContinuous.1,
    Filtration.usualAugmentation_eq_withNullSets rawFiltrations_rightContinuous.2]
  intro t
  change rawSmallFiltration t ⊔ Filtration.nullSets sampleMeasure ≤
    rawMagnitudeFiltration t ⊔ Filtration.nullSets sampleMeasure
  apply sup_le_sup_right
  by_cases ht : (1 : ℝ≥0) ≤ t
  · change (if 1 ≤ t then _ else _) ≤ if 1 ≤ t then _ else _
    simp only [if_pos ht, le_refl]
  · change (if 1 ≤ t then _ else ⊥) ≤ if 1 ≤ t then _ else _
    simp only [if_neg ht]
    exact bot_le

theorem revealProcess_isLocalMartingale_magnitude :
    IsLocalMartingale (fun t (x : NullMeasurableSpace ℝ sampleMeasure) ↦ revealProcess t x)
      magnitudeFiltration sampleMeasure.completion :=
  revealProcess_isLocalMartingale_rawMagnitude.usualAugmentation_of_isRightContinuous
    rawFiltrations_rightContinuous.2

private theorem small_before_one :
    (isStoppingTime_const smallFiltration (1 : ℝ≥0)).measurableSpaceBefore =
      Filtration.nullSets sampleMeasure := by
  have ht (t : ℝ≥0) (ht : t < 1) :
      smallFiltration t = Filtration.nullSets sampleMeasure := by
    rw [smallFiltration,
      Filtration.usualAugmentation_eq_withNullSets rawFiltrations_rightContinuous.1]
    change (if 1 ≤ t then _ else ⊥) ⊔ Filtration.nullSets sampleMeasure = _
    simp only [if_neg (not_le.mpr ht), bot_sup_eq]
  rw [IsStoppingTime.measurableSpaceBefore_const, ht 0 zero_lt_one]
  apply le_antisymm
  · exact sup_le le_rfl (iSup_le fun t ↦ iSup_le fun h ↦ (ht t h).le)
  · exact le_sup_left

private theorem before_one_zero_one (s : Set (NullMeasurableSpace ℝ sampleMeasure))
    (hs : MeasurableSet[(isStoppingTime_const smallFiltration (1 : ℝ≥0)).measurableSpaceBefore]
      s) : sampleMeasure.completion s = 0 ∨ sampleMeasure.completion s = 1 := by
  rw [small_before_one] at hs
  have hs' : MeasurableSet[(⊥ : MeasurableSpace ℝ) ⊔ Filtration.nullSets sampleMeasure] s := by
    rw [bot_sup_eq]
    exact hs
  obtain ⟨B, hB, he⟩ :=
    (measurableSet_sup_nullSets_iff (m := ⊥) (P := sampleMeasure)).mp hs'
  have heP : sampleMeasure.completion s = sampleMeasure.completion B :=
    measure_congr (show s =ᵐ[sampleMeasure.completion] B from he)
  rcases MeasurableSpace.measurableSet_bot_iff.mp hB with rfl | rfl
  · exact Or.inl (heP.trans measure_empty)
  · exact Or.inr (heP.trans (measure_univ : sampleMeasure.completion univ = 1))

/-- Initially hiding the magnitude prevents any native L1 localizing sequence. -/
theorem revealProcess_not_isLocalMartingale_small :
    ¬ IsLocalMartingale (fun t (x : NullMeasurableSpace ℝ sampleMeasure) ↦ revealProcess t x)
      smallFiltration sampleMeasure.completion := by
  intro h
  have hlp : Locally (fun Y : ℝ≥0 → NullMeasurableSpace ℝ sampleMeasure → ℝ ↦
      ∀ t, MemLp (Y t) 1 sampleMeasure.completion) smallFiltration
      (fun t x ↦ revealProcess t x) sampleMeasure.completion :=
    Locally.mono (fun _ hY t ↦ memLp_one_iff_integrable.mpr (hY.1.integrable t)) h.locally_ui
  have h1 := hlp.memLp_at_of_before_zero_one (T := 1) zero_lt_one before_one_zero_one
  have hi : Integrable (fun x : NullMeasurableSpace ℝ sampleMeasure ↦ value x)
      sampleMeasure.completion := by
    apply memLp_one_iff_integrable.mp
    simpa only [revealProcess, le_refl, if_true] using h1
  have hle : (inferInstance : MeasurableSpace ℝ) ≤
      (inferInstance : MeasurableSpace (NullMeasurableSpace ℝ sampleMeasure)) :=
    fun _ hs ↦ hs.nullMeasurableSet
  have htrim : sampleMeasure.completion.trim hle = sampleMeasure := by
    apply @Measure.ext ℝ (inferInstance : MeasurableSpace ℝ)
    intro s hs
    exact (trim_measurableSet_eq (μ := sampleMeasure.completion) hle hs).trans rfl
  apply not_integrable_value
  rw [← htrim]
  exact Integrable.trim hle hi measurable_value.stronglyMeasurable

private theorem revealProcess_adapted_rawSmall : Adapted rawSmallFiltration revealProcess := by
  intro t
  by_cases ht : (1 : ℝ≥0) ≤ t
  · have hf : rawSmallFiltration t = (inferInstance : MeasurableSpace ℝ) := if_pos ht
    have he : revealProcess t = value := by funext x; exact if_pos ht
    change Measurable[rawSmallFiltration t] (revealProcess t)
    rw [hf, he]
    exact measurable_value
  · have he : revealProcess t = fun _ ↦ 0 := by funext x; exact if_neg ht
    change Measurable[rawSmallFiltration t] (revealProcess t)
    rw [he]
    exact measurable_const

private theorem revealProcess_finiteVariation (x : ℝ) :
    LocallyBoundedVariationOn (revealProcess · x) univ := by
  have hm : Monotone (fun t : ℝ≥0 ↦ if 1 ≤ t then (1 : ℝ) else 0) := by
    intro s t hst
    by_cases hs : (1 : ℝ≥0) ≤ s
    · simp only [if_pos hs, if_pos (hs.trans hst), le_refl]
    · simp only [if_neg hs]
      split_ifs <;> norm_num
  have hc : Monotone (fun _ : ℝ≥0 ↦ value x) := monotone_const
  have hv := (hc.monotoneOn univ).locallyBoundedVariationOn.mul
    (hm.monotoneOn univ).locallyBoundedVariationOn
  convert! hv using 1
  ext t
  simp only [Pi.mul_apply, revealProcess]
  split_ifs <;> simp

/-- The same process remains an actual finite-variation semimartingale after shrinking. -/
theorem revealProcess_isSemimartingale_small :
    IsSemimartingale (fun t (x : NullMeasurableSpace ℝ sampleMeasure) ↦ revealProcess t x)
      smallFiltration sampleMeasure.completion := by
  have ha : Adapted smallFiltration
      (fun t (x : NullMeasurableSpace ℝ sampleMeasure) ↦ revealProcess t x) :=
    fun t ↦ (revealProcess_adapted_rawSmall t).mono
      (rawSmallFiltration.le_usualAugmentation sampleMeasure t) le_rfl
  exact (show HasFiniteVariationPaths
      (fun t (x : NullMeasurableSpace ℝ sampleMeasure) ↦ revealProcess t x)
      sampleMeasure.completion from ae_of_all _ revealProcess_finiteVariation).isSemimartingale
    ha completedFiltrations_usual_and_le.1 (ae_of_all _ revealProcess_isCadlagPath)

end StochLean.SymmetricInverseModel
