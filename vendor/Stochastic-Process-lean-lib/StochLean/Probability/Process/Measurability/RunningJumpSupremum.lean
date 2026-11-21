/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.Path.RunningJumpSupremum
public import StochLean.Probability.Process.Stopping.LargeJumpTimes
public import StochLean.Probability.Process.Measurability.CadlagVersion

/-! # Adaptedness of the actual all-times running jump supremum

At a strictly positive threshold, exceeding the threshold means either that
the initial jump already exceeds it or that the actual first positive-time
large jump has occurred. Cadlag finite attainment retains the closed terminal
endpoint. Countably many rational thresholds give measurability of the
original extended supremum; no dense grid of jump times is substituted.

For AE-cadlag paths, an everywhere-cadlag version supplies the measurable
representative. Common jump equality and usual completeness then recover
adaptedness of the original all-times supremum, not only of a replacement.
-/

@[expose] public section

open MeasureTheory Filter Set
open scoped NNReal ENNReal

namespace ProbabilityTheory

variable {Ω : Type*} {X : ℝ≥0 → Ω → ℝ} {ω : Ω}

/-- Strict positive-threshold exceedance retains both the initial jump and
the actual first large jump at the closed horizon. -/
theorem IsCadlagPath.lt_eRunningJumpSupremum_iff
    (hX : IsCadlagPath (X · ω)) {a : ℝ} (ha : 0 < a) (T : ℝ≥0) :
    ENNReal.ofReal a < eRunningJumpSupremum X T ω ↔
      a < ‖X 0 ω‖ ∨ nextLargeJump X a (fun _ ↦ 0) ω ≤ (T : WithTop ℝ≥0) := by
  constructor
  · intro h
    obtain ⟨t, ht, hj⟩ := (by simpa only [eRunningJumpSupremum, lt_iSup_iff] using h :
      ∃ t : ℝ≥0, ∃ _ : t ≤ T, ENNReal.ofReal a < ENNReal.ofReal ‖jumpProcess X t ω‖)
    have hj' := (ENNReal.ofReal_lt_ofReal_iff_of_nonneg ha.le).mp hj
    by_cases ht0 : t = 0
    · left
      simpa only [ht0, jumpProcess_zero] using hj'
    · right
      exact (nextLargeJump_le_of_jump (X := X) (σ := fun _ ↦ 0) (ω := ω)
        (show (0 : WithTop ℝ≥0) < t from WithTop.coe_lt_coe.mpr (pos_iff_ne_zero.mpr ht0))
        hj').trans (WithTop.coe_le_coe.mpr ht)
  · rintro (h0 | hT)
    · have hbase : ENNReal.ofReal ‖X 0 ω‖ ≤ eRunningJumpSupremum X T ω := by
        change ENNReal.ofReal ‖X 0 ω‖ ≤
          ⨆ t : ℝ≥0, ⨆ (_ : t ≤ T), ENNReal.ofReal ‖jumpProcess X t ω‖
        exact le_iSup_of_le 0 (le_iSup_of_le bot_le (by rw [jumpProcess_zero]))
      exact ((ENNReal.ofReal_lt_ofReal_iff_of_nonneg ha.le).mpr h0).trans_le hbase
    · have hfin : nextLargeJump X a (fun _ ↦ 0) ω ≠ ⊤ :=
        ne_top_of_le_ne_top WithTop.coe_ne_top hT
      obtain ⟨t, ht, _, hj, _⟩ := hX.nextLargeJump_spec ha hfin
      have htT : t ≤ T := WithTop.coe_le_coe.mp (ht ▸ hT)
      exact ((ENNReal.ofReal_lt_ofReal_iff_of_nonneg ha.le).mpr hj).trans_le
        (le_iSup_of_le t (le_iSup_of_le htT le_rfl))

variable {mΩ : MeasurableSpace Ω} {P : Measure Ω} {Y : ℝ≥0 → Ω → ℝ}

/-- Common path equality transports the actual uncountable jump supremum. -/
theorem Indistinguishable.eRunningJumpSupremum (he : Indistinguishable X Y P) :
    Indistinguishable (eRunningJumpSupremum X) (eRunningJumpSupremum Y) P := by
  filter_upwards [he.jumpProcess] with ω hω T
  change (⨆ t : ℝ≥0, ⨆ (_ : t ≤ T), ENNReal.ofReal ‖ProbabilityTheory.jumpProcess X t ω‖) =
    ⨆ t : ℝ≥0, ⨆ (_ : t ≤ T), ENNReal.ofReal ‖ProbabilityTheory.jumpProcess Y t ω‖
  simp only [hω]

end ProbabilityTheory

namespace MeasureTheory

open ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {F : Filtration ℝ≥0 mΩ}
  {X : ℝ≥0 → Ω → ℝ} {P : Measure Ω}

/-- Rational positive-threshold events prove measurability of the original
all-times extended jump supremum, including its initial jump. -/
theorem Adapted.measurable_eRunningJumpSupremum_of_cadlag [F.IsRightContinuous]
    (ha : Adapted F X) (hc : ∀ ω, IsCadlagPath (X · ω)) (T : ℝ≥0) :
    Measurable[F T] (eRunningJumpSupremum X T) := by
  have hpos (a : ℝ) (ha0 : 0 < a) :
      MeasurableSet[F T] {ω | ENNReal.ofReal a < eRunningJumpSupremum X T ω} := by
    have he : {ω | ENNReal.ofReal a < eRunningJumpSupremum X T ω} =
        {ω | a < ‖X 0 ω‖} ∪
          {ω | nextLargeJump X a (fun _ ↦ 0) ω ≤ (T : WithTop ℝ≥0)} := by
      ext ω
      exact (hc ω).lt_eRunningJumpSupremum_iff ha0 T
    rw [he]
    have hm0 : Measurable[F T] (X 0) := (ha 0).mono (F.mono bot_le) le_rfl
    exact (measurableSet_lt measurable_const (measurable_norm.comp hm0)).union
      (ha.isStoppingTime_nextLargeJump hc ha0 (isStoppingTime_const F 0) T)
  apply measurable_of_Ioi
  intro a
  have he : (eRunningJumpSupremum X T) ⁻¹' Ioi a =
      ⋃ q : ℚ, ⋃ (_ : 0 ≤ q), ⋃ (_ : a < ENNReal.ofReal (q : ℝ)),
        {ω | ENNReal.ofReal (q : ℝ) < eRunningJumpSupremum X T ω} := by
    ext ω
    simpa only [mem_preimage, mem_Ioi, mem_iUnion, mem_ofPred_eq, exists_prop,
      ENNReal.ofReal] using
      (ENNReal.lt_iff_exists_rat_btwn (a := a) (b := eRunningJumpSupremum X T ω))
  rw [he]
  apply MeasurableSet.iUnion
  intro q
  apply MeasurableSet.iUnion
  intro _
  apply MeasurableSet.iUnion
  intro haq
  exact hpos q (ENNReal.ofReal_pos.mp (bot_le.trans_lt haq))

/-- Usual completeness gives adaptedness of the actual jump supremum even
when cadlag paths hold only almost surely. No moment or finite-measure
assumption is needed. Its real conversion is therefore also adapted. -/
theorem Adapted.eRunningJumpSupremum_of_usual
    (ha : Adapted F X) (hF : F.IsUsual P) (hc : HasCadlagPaths X P) :
    Adapted F (eRunningJumpSupremum X) := by
  let : F.IsRightContinuous := hF.rightContinuous
  obtain ⟨Y, he, hpY, hcY⟩ :=
    ha.stronglyAdapted.exists_cadlag_indistinguishable_of_usual hF hc
  have hm := hpY.stronglyAdapted.adapted.measurable_eRunningJumpSupremum_of_cadlag hcY
  have heJ := he.eRunningJumpSupremum
  intro T
  have hcomplete : IsCompleteSubMeasurableSpace P (F T) :=
    fun s hs ↦ F.mono bot_le s (hF.complete_initial s hs)
  exact hcomplete.measurable_congr_ae (hm T) (heJ.symm.mono fun _ hω ↦ hω T)

end MeasureTheory
