/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.LocalMartingale.BeforeFieldMoment
public import StochLean.Probability.Process.LocalMartingale.GeometricMomentModel
public import StochLean.Probability.Martingale.Doob.CenteredSingleJump
public import StochLean.Probability.Process.Filtration.Usual
public import StochLean.Probability.Process.Path.RightStep

/-! # A UI local martingale which is not locally square-integrable

The actual geometric random variable `value n = 2^n` is revealed at time one.
The centered closed step starts at zero and is a true UI martingale. Its
filtration is genuinely usual: every singleton has positive probability, so
the trivial initial sigma-field contains all null sets.

Nevertheless, the process does not satisfy native local square integrability.
The sigma-field strictly before one is trivial. The before-field moment
result therefore turns any proposed native L2 localizing sequence into an
L2 bound on the original coordinate at one, contradicting the actual infinite
second moment of `value`. The positive-lifetime mask is retained throughout.

This is a concrete version of Protter's first example on printed page 128.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal

namespace StochLean.GeometricMomentModel

/-- The sample is first revealed at time one. -/
noncomputable def revealFiltration :
    Filtration ℝ≥0 (inferInstance : MeasurableSpace ℕ) where
  seq t := if 1 ≤ t then ⊤ else ⊥
  mono' := by
    intro s t hst
    by_cases hs : (1 : ℝ≥0) ≤ s
    · simp only [if_pos hs, if_pos (hs.trans hst), le_refl]
    · simp only [if_neg hs]
      exact bot_le
  le' _ := le_top

/-- The actual integrable centered jump, with zero initial value. -/
noncomputable def jumpMartingale (t : ℝ≥0) (n : ℕ) : ℝ :=
  if 1 ≤ t then value n - 3 / 2 else 0

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

/-- Positive mass at every sample makes the actual initial field complete. -/
theorem revealFiltration_isUsual : revealFiltration.IsUsual sampleMeasure := by
  refine ⟨reveal_rightContinuous, ?_⟩
  intro s hs
  have he : s = ∅ := by
    apply eq_empty_iff_forall_notMem.mpr
    intro n hn
    exact (sampleMeasure_singleton_pos n).ne'
      (measure_mono_null (singleton_subset_iff.mpr hn) hs)
  rw [he]
  exact @MeasurableSet.empty _ (revealFiltration ⊥)

private theorem reveal_before_one :
    (isStoppingTime_const revealFiltration (1 : ℝ≥0)).measurableSpaceBefore = ⊥ := by
  rw [IsStoppingTime.measurableSpaceBefore_const]
  apply bot_unique
  refine sup_le ?_ (iSup_le fun t ↦ iSup_le fun ht ↦ ?_)
  · change (if (1 : ℝ≥0) ≤ 0 then ⊤ else ⊥) ≤ ⊥
    norm_num
  · change (if 1 ≤ t then ⊤ else ⊥) ≤ ⊥
    simp only [if_neg (not_le.mpr ht), le_refl]

theorem jumpMartingale_isCadlagPath (n : ℕ) :
    IsCadlagPath (jumpMartingale · n) :=
  isCadlagPath_step_Ici 1 (value n - 3 / 2)

/-- The previously proved actual mean centers this single jump before time one. -/
theorem jumpMartingale_isUIMartingale :
    IsUIMartingale jumpMartingale revealFiltration sampleMeasure := by
  let hτ := isStoppingTime_const revealFiltration (1 : ℝ≥0)
  have hm : StronglyMeasurable[hτ.measurableSpace] value := by
    rw [IsStoppingTime.measurableSpace_const]
    have h1 : revealFiltration 1 = (inferInstance : MeasurableSpace ℕ) := by
      change (if (1 : ℝ≥0) ≤ 1 then ⊤ else ⊥) = ⊤
      exact if_pos le_rfl
    rw [h1]
    exact .of_discrete
  have hu := isUIMartingale_indicator_sub_condExp_before hτ hm integrable_value
  rw [reveal_before_one, condExp_bot, integral_value] at hu
  change IsUIMartingale (fun (t : ℝ≥0) (n : ℕ) ↦
    {k : ℕ | ((1 : ℝ≥0) : WithTop ℝ≥0) ≤ (t : WithTop ℝ≥0)}.indicator
      (value - fun _ ↦ 3 / 2) n) revealFiltration sampleMeasure at hu
  change IsUIMartingale (fun (t : ℝ≥0) (n : ℕ) ↦ if 1 ≤ t then value n - 3 / 2 else 0)
    revealFiltration sampleMeasure
  simpa only [indicator_apply, mem_ofPred_eq, WithTop.coe_le_coe,
    Pi.sub_apply] using hu

theorem jumpMartingale_isLocalMartingale :
    IsLocalMartingale jumpMartingale revealFiltration sampleMeasure :=
  jumpMartingale_isUIMartingale.isLocalMartingale
    (ae_of_all _ jumpMartingale_isCadlagPath)

/-- Even native masked localization cannot make this actual UI martingale L2. -/
theorem jumpMartingale_not_locally_squareIntegrable :
    ¬ Locally (fun Y ↦ IsSquareIntegrableMartingale Y revealFiltration sampleMeasure)
      revealFiltration jumpMartingale sampleMeasure := by
  intro h
  have hlp : Locally (fun Y : ℝ≥0 → ℕ → ℝ ↦ ∀ t, MemLp (Y t) 2 sampleMeasure)
      revealFiltration jumpMartingale sampleMeasure := Locally.mono (fun _ hY ↦ hY.2) h
  have h1 : MemLp (jumpMartingale 1) 2 sampleMeasure :=
    hlp.memLp_at_of_before_zero_one (by norm_num) (by
      intro s hs
      rw [reveal_before_one] at hs
      rcases MeasurableSpace.measurableSet_bot_iff.mp hs with rfl | rfl
      · exact Or.inl measure_empty
      · exact Or.inr measure_univ)
  have hc : MemLp (fun _ : ℕ ↦ (3 / 2 : ℝ)) 2 sampleMeasure := memLp_const _
  apply not_memLp_two
  convert! h1.add hc using 1
  ext n
  simp only [Pi.add_apply, jumpMartingale, le_refl, if_true, sub_add_cancel]

end StochLean.GeometricMomentModel
