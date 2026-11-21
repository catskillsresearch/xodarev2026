/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.LocalMartingale.SymmetricInverseModel
public import StochLean.Probability.Process.LocalMartingale.InitialValue
public import StochLean.Probability.Martingale.Doob.CenteredSingleJump
public import StochLean.Probability.Process.Path.RightStep

/-! # A non-integrable jump localized by initially known magnitude

The fixed symmetric inverse random variable is revealed at time one. The
larger raw filtration initially knows its absolute value. Each actual bounded
magnitude cutoff has conditional mean zero in that initial field, proved by
reflection on every initial-field event. The existing initial-value localizer
of the magnitude then gives a native fundamental sequence for the reveal
process, despite the original coefficient having no first moment.

Both raw filtrations are right-continuous. Neither is asserted usual on the
original Borel probability space; genuine completion is a separate consumer.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology

namespace StochLean.SymmetricInverseModel

private theorem measurable_magnitude : Measurable (fun x ↦ |value x|) := by
  simpa only [Real.norm_eq_abs] using measurable_value.norm

/-- The smaller raw filtration first sees the sample at time one. -/
noncomputable def rawSmallFiltration : Filtration ℝ≥0 (inferInstance : MeasurableSpace ℝ) where
  seq t := if 1 ≤ t then inferInstance else ⊥
  mono' := by
    intro s t hst
    by_cases hs : (1 : ℝ≥0) ≤ s
    · simp only [if_pos hs, if_pos (hs.trans hst), le_refl]
    · simp only [if_neg hs]
      exact bot_le
  le' t := by split_ifs <;> first | exact le_rfl | exact bot_le

/-- The larger raw filtration initially knows precisely the value's magnitude. -/
noncomputable def rawMagnitudeFiltration :
    Filtration ℝ≥0 (inferInstance : MeasurableSpace ℝ) where
  seq t := if 1 ≤ t then inferInstance else
    MeasurableSpace.comap (fun x ↦ |value x|) (inferInstance : MeasurableSpace ℝ)
  mono' := by
    intro s t hst
    by_cases hs : (1 : ℝ≥0) ≤ s
    · simp only [if_pos hs, if_pos (hs.trans hst), le_refl]
    · simp only [if_neg hs]
      split_ifs
      · exact measurable_magnitude.comap_le
      · exact le_rfl
  le' t := by
    split_ifs
    · exact le_rfl
    · exact measurable_magnitude.comap_le

/-- The original non-integrable coefficient activates at the closed time one. -/
noncomputable def revealProcess (t : ℝ≥0) (x : ℝ) : ℝ :=
  if 1 ≤ t then value x else 0

private theorem rawSmall_rightContinuous : rawSmallFiltration.IsRightContinuous := by
  constructor
  intro t
  rw [Filtration.rightCont_eq]
  by_cases ht : (1 : ℝ≥0) ≤ t
  · apply iInf₂_le_of_le (t + 1) (lt_add_one t)
    change (if 1 ≤ t + 1 then _ else ⊥) ≤ if 1 ≤ t then _ else ⊥
    simp only [if_pos ht, if_pos (ht.trans (le_add_of_nonneg_right zero_le_one)), le_refl]
  · obtain ⟨u, htu, hu⟩ := exists_between (lt_of_not_ge ht)
    apply iInf₂_le_of_le u htu
    change (if 1 ≤ u then _ else ⊥) ≤ if 1 ≤ t then _ else ⊥
    simp only [if_neg (not_le.mpr hu), if_neg ht, le_refl]

private theorem rawMagnitude_rightContinuous : rawMagnitudeFiltration.IsRightContinuous := by
  constructor
  intro t
  rw [Filtration.rightCont_eq]
  by_cases ht : (1 : ℝ≥0) ≤ t
  · apply iInf₂_le_of_le (t + 1) (lt_add_one t)
    change (if 1 ≤ t + 1 then _ else _) ≤ if 1 ≤ t then _ else _
    simp only [if_pos ht, if_pos (ht.trans (le_add_of_nonneg_right zero_le_one)), le_refl]
  · obtain ⟨u, htu, hu⟩ := exists_between (lt_of_not_ge ht)
    apply iInf₂_le_of_le u htu
    change (if 1 ≤ u then _ else _) ≤ if 1 ≤ t then _ else _
    simp only [if_neg (not_le.mpr hu), if_neg ht, le_refl]

theorem rawFiltrations_rightContinuous :
    rawSmallFiltration.IsRightContinuous ∧ rawMagnitudeFiltration.IsRightContinuous :=
  ⟨rawSmall_rightContinuous, rawMagnitude_rightContinuous⟩

private theorem magnitude_before_one :
    (isStoppingTime_const rawMagnitudeFiltration (1 : ℝ≥0)).measurableSpaceBefore =
      MeasurableSpace.comap (fun x ↦ |value x|) (inferInstance : MeasurableSpace ℝ) := by
  rw [IsStoppingTime.measurableSpaceBefore_const]
  apply le_antisymm
  · refine sup_le ?_ (iSup_le fun t ↦ iSup_le fun ht ↦ ?_)
    · change (if (1 : ℝ≥0) ≤ 0 then _ else _) ≤ _
      simp only [not_le.mpr zero_lt_one, if_false, le_refl]
    · change (if 1 ≤ t then _ else _) ≤ _
      simp only [if_neg (not_le.mpr ht), le_refl]
  · apply le_sup_of_le_left
    change _ ≤ if (1 : ℝ≥0) ≤ 0 then _ else _
    simp only [not_le.mpr zero_lt_one, if_false, le_refl]

private theorem magnitude_event_reflection {s : Set ℝ}
    (hs : MeasurableSet[MeasurableSpace.comap (fun x ↦ |value x|)
      (inferInstance : MeasurableSpace ℝ)] s) :
    (fun x : ℝ ↦ -x) ⁻¹' s = s := by
  obtain ⟨B, _, rfl⟩ := MeasurableSpace.measurableSet_comap.mp hs
  ext x
  simp only [mem_preimage, value, inv_neg, abs_neg]

private theorem integral_cutoff_on_magnitude_event (n : ℕ) {s : Set ℝ}
    (hs : MeasurableSet[MeasurableSpace.comap (fun x ↦ |value x|)
      (inferInstance : MeasurableSpace ℝ)] s) :
    ∫ x in s, {x | |value x| ≤ (n : ℝ)}.indicator value x ∂sampleMeasure = 0 := by
  let K : ℝ → ℝ := {x | |value x| ≤ (n : ℝ)}.indicator value
  have hr := measurePreserving_neg.restrict_preimage (measurable_magnitude.comap_le _ hs)
  rw [magnitude_event_reflection hs] at hr
  have hodd (x : ℝ) : K (-x) = -K x := by
    simp only [K, indicator_apply, mem_ofPred_eq, value, inv_neg, abs_neg]
    split_ifs <;> simp
  have he := hr.integral_comp measurableEmbedding_neg K
  simp only [hodd, integral_neg] at he
  change (∫ x, K x ∂sampleMeasure.restrict s) = 0
  linarith

/-- Actual bounded cutoffs are L1 and centered given the initially known magnitude. -/
theorem integrable_cutoff_and_condExp_magnitude_eq_zero (n : ℕ) :
    Integrable ({x | |value x| ≤ (n : ℝ)}.indicator value) sampleMeasure ∧
      sampleMeasure[{x | |value x| ≤ (n : ℝ)}.indicator value |
        MeasurableSpace.comap (fun x ↦ |value x|) (inferInstance : MeasurableSpace ℝ)]
          =ᵐ[sampleMeasure] 0 := by
  have hm : Measurable ({x | |value x| ≤ (n : ℝ)}.indicator value) :=
    measurable_value.indicator (measurableSet_le measurable_magnitude measurable_const)
  have hi : Integrable ({x | |value x| ≤ (n : ℝ)}.indicator value) sampleMeasure := by
    apply (integrable_const (n : ℝ)).mono' hm.aestronglyMeasurable
    apply ae_of_all
    intro x
    by_cases hx : |value x| ≤ (n : ℝ)
    · simpa only [indicator_of_mem (show x ∈ {x | |value x| ≤ (n : ℝ)} from hx),
        Real.norm_eq_abs] using hx
    · simp only [indicator_of_notMem
        (show x ∉ {x | |value x| ≤ (n : ℝ)} from hx), norm_zero]
      exact Nat.cast_nonneg n
  refine ⟨hi, ?_⟩
  apply Filter.EventuallyEq.symm
  refine ae_eq_condExp_of_forall_setIntegral_eq measurable_magnitude.comap_le hi
    (fun _ _ _ ↦ (show Integrable (fun _ : ℝ ↦ (0 : ℝ)) sampleMeasure from
      integrable_const 0).integrableOn) ?_ aestronglyMeasurable_zero
  intro s hs _
  simpa only [Pi.zero_apply, integral_zero] using
    (integral_cutoff_on_magnitude_event n hs).symm

private theorem isUIMartingale_cutoff_reveal (n : ℕ) :
    IsUIMartingale (fun (t : ℝ≥0) (x : ℝ) ↦
      if 1 ≤ t then {x | |value x| ≤ (n : ℝ)}.indicator value x else 0)
      rawMagnitudeFiltration sampleMeasure := by
  let hτ := isStoppingTime_const rawMagnitudeFiltration (1 : ℝ≥0)
  have hm : StronglyMeasurable[hτ.measurableSpace]
      ({x | |value x| ≤ (n : ℝ)}.indicator value) := by
    rw [IsStoppingTime.measurableSpace_const]
    change StronglyMeasurable[if (1 : ℝ≥0) ≤ 1 then _ else _] _
    rw [if_pos le_rfl]
    exact (measurable_value.indicator
      (measurableSet_le measurable_magnitude measurable_const)).stronglyMeasurable
  have hi := integrable_cutoff_and_condExp_magnitude_eq_zero n
  have hz : sampleMeasure[{x | |value x| ≤ (n : ℝ)}.indicator value |
      hτ.measurableSpaceBefore] =ᵐ[sampleMeasure] 0 := by
    rw [magnitude_before_one]
    exact hi.2
  have hu := isUIMartingale_indicator_stoppingTime_le_of_condExp_before_eq_zero
    hτ hm hi.1 hz
  change IsUIMartingale (fun (t : ℝ≥0) (x : ℝ) ↦
    {y : ℝ | ((1 : ℝ≥0) : WithTop ℝ≥0) ≤ (t : WithTop ℝ≥0)}.indicator
      ({x | |value x| ≤ (n : ℝ)}.indicator value) x) rawMagnitudeFiltration sampleMeasure at hu
  simpa only [indicator_apply, mem_ofPred_eq, WithTop.coe_le_coe] using hu

theorem revealProcess_isCadlagPath (x : ℝ) : IsCadlagPath (revealProcess · x) :=
  isCadlagPath_step_Ici 1 (value x)

/-- The existing magnitude localizer gives an actual native fundamental sequence. -/
theorem revealProcess_isLocalMartingale_rawMagnitude :
    IsLocalMartingale revealProcess rawMagnitudeFiltration sampleMeasure := by
  have ha : Adapted rawMagnitudeFiltration revealProcess := by
    intro t
    by_cases ht : (1 : ℝ≥0) ≤ t
    · have hf : rawMagnitudeFiltration t = (inferInstance : MeasurableSpace ℝ) :=
        if_pos ht
      have he : revealProcess t = value := by funext x; exact if_pos ht
      change Measurable[rawMagnitudeFiltration t] (revealProcess t)
      rw [hf, he]
      exact measurable_value
    · have he : revealProcess t = fun _ ↦ 0 := by funext x; exact if_neg ht
      change Measurable[rawMagnitudeFiltration t] (revealProcess t)
      rw [he]
      exact measurable_const
  have hmag : Measurable[rawMagnitudeFiltration 0] (fun x ↦ |value x|) := by
    change Measurable[if (1 : ℝ≥0) ≤ 0 then _ else _] _
    rw [if_neg (not_le.mpr zero_lt_one)]
    exact comap_measurable _
  refine ⟨ha, ae_of_all _ revealProcess_isCadlagPath,
    initialValueLocalizer (fun x ↦ |value x|), ?_⟩
  refine ⟨⟨initialValueLocalizer_isStoppingTime hmag,
    ae_of_all _ (initialValueLocalizer_tendsto _)⟩,
    initialValueLocalizer_monotone _, fun n ↦ ?_⟩
  have he : stoppedProcess (fun t ↦
      {x | 0 < initialValueLocalizer (fun x ↦ |value x|) n x}.indicator (revealProcess t))
      (initialValueLocalizer (fun x ↦ |value x|) n) =
      fun (t : ℝ≥0) (x : ℝ) ↦
        if 1 ≤ t then {x | |value x| ≤ (n : ℝ)}.indicator value x else 0 := by
    funext t x
    by_cases hx : |value x| ≤ (n : ℝ)
    · have hτ : initialValueLocalizer (fun x ↦ |value x|) n x = ⊤ := by
        simp only [initialValueLocalizer, abs_abs, if_pos hx]
      rw [stoppedProcess_eq_of_le (show (t : WithTop ℝ≥0) ≤
        initialValueLocalizer (fun x ↦ |value x|) n x from hτ ▸ le_top)]
      simp [hτ, revealProcess, hx]
    · simp [initialValueLocalizer, abs_abs, hx, stoppedProcess]
  rw [he]
  exact isUIMartingale_cutoff_reveal n

end StochLean.SymmetricInverseModel
