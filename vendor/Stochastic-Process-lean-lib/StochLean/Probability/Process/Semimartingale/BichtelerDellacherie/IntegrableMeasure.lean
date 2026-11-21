/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.Path.RunningJumpSupremum
public import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
public import Mathlib.MeasureTheory.Function.L1Space.Integrable

/-! # An equivalent finite-horizon integrability measure

This is Protter III.47, Lemma 2.  A measurable reciprocal weight built from
the countable compact running norm supremum makes every coordinate on a fixed
horizon integrable.  Càdlàg boundedness is used only on its common full-measure
event; the density itself is strictly positive everywhere.
-/

@[expose] public section

open MeasureTheory Filter
open scoped NNReal ENNReal

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

/-- Strictly positive bounded weight attached to the compact running norm
supremum of a process. -/
noncomputable def compactCadlagWeight (X : ℝ≥0 → Ω → ℝ) (T : ℝ≥0) : Ω → ℝ≥0 :=
  fun ω ↦ Real.toNNReal
    ((1 + (denseRunningSupremum (fun t v ↦ ‖X t v‖) T ω).toReal)⁻¹)

theorem coe_compactCadlagWeight (X : ℝ≥0 → Ω → ℝ) (T : ℝ≥0) (ω : Ω) :
    (compactCadlagWeight X T ω : ℝ) =
      (1 + (denseRunningSupremum (fun t v ↦ ‖X t v‖) T ω).toReal)⁻¹ := by
  rw [compactCadlagWeight, Real.coe_toNNReal]
  positivity

theorem compactCadlagWeight_pos (X : ℝ≥0 → Ω → ℝ) (T : ℝ≥0) (ω : Ω) :
    0 < compactCadlagWeight X T ω := by
  rw [← NNReal.coe_pos, coe_compactCadlagWeight]
  positivity

theorem measurable_compactCadlagWeight {F : Filtration ℝ≥0 mΩ}
    {X : ℝ≥0 → Ω → ℝ} (ha : Adapted F X) (T : ℝ≥0) :
    Measurable (compactCadlagWeight X T) := by
  apply Measurable.real_toNNReal
  apply Measurable.inv
  exact measurable_const.add
    (measurable_toReal_denseRunningSupremum
      (fun t ↦ (continuous_norm.measurable.comp
        ((ha t).mono (F.le t) le_rfl))) T)

/-- The reciprocal running-supremum weight controls every coordinate on the
fixed horizon by one on the common càdlàg event. -/
theorem compactCadlagWeight_mul_norm_le_one_ae
    {P : Measure Ω} {X : ℝ≥0 → Ω → ℝ}
    (hc : HasCadlagPaths X P) (T : ℝ≥0) :
    ∀ᵐ ω ∂P, ∀ t, t ≤ T →
      (compactCadlagWeight X T ω : ℝ) * ‖X t ω‖ ≤ 1 := by
  filter_upwards [hc] with ω hω
  intro t ht
  let S := (denseRunningSupremum (fun s v ↦ ‖X s v‖) T ω).toReal
  have hfin := hω.denseRunningSupremum_norm_ne_top T
  have hrc : IsRightContinuousPath (fun s ↦ ‖X s ω‖) :=
    fun s ↦ continuous_norm.continuousAt.comp_continuousWithinAt (hω.1 s)
  have hle : ‖X t ω‖ ≤ S :=
    le_toReal_denseRunningSupremum_of_rightContinuous ht hrc hfin
  rw [coe_compactCadlagWeight]
  change (1 + S)⁻¹ * ‖X t ω‖ ≤ 1
  rw [inv_mul_eq_div]
  exact (div_le_one (by positivity : 0 < 1 + S)).2 (hle.trans (le_add_of_nonneg_left zero_le_one))

/-- Data of a probability law equivalent to the source law under which all
process coordinates on one deterministic compact horizon are integrable. -/
structure EquivalentIntegrabilityMeasure (X : ℝ≥0 → Ω → ℝ)
    (T : ℝ≥0) (P : Measure Ω) where
  measure : Measure Ω
  isProbabilityMeasure : IsProbabilityMeasure measure
  absolutelyContinuous : measure ≪ P
  sourceAbsolutelyContinuous : P ≪ measure
  dominated : ∃ C : ℝ≥0∞, C ≠ ∞ ∧ measure ≤ C • P
  integrable_compactSup :
    Integrable (fun ω ↦
      (denseRunningSupremum (fun t v ↦ ‖X t v‖) T ω).toReal) measure
  integrable : ∀ t, t ≤ T → Integrable (X t) measure

variable {F : Filtration ℝ≥0 mΩ} {P : Measure Ω} {X : ℝ≥0 → Ω → ℝ}
  [IsProbabilityMeasure P]

/-- Protter III.47, Lemma 2: every adapted càdlàg process admits an equivalent
probability law with finite first moments on a prescribed compact horizon. -/
theorem exists_equivalentIntegrabilityMeasure
    (ha : Adapted F X) (hc : HasCadlagPaths X P) (T : ℝ≥0) :
    Nonempty (EquivalentIntegrabilityMeasure X T P) := by
  let d : Ω → ℝ≥0 := compactCadlagWeight X T
  have hd : Measurable d := measurable_compactCadlagWeight ha T
  let ν : Measure Ω := P.withDensity fun ω ↦ (d ω : ℝ≥0∞)
  have hdle : ∀ ω, (d ω : ℝ≥0∞) ≤ 1 := by
    intro ω
    rw [← ENNReal.coe_one, ENNReal.coe_le_coe]
    rw [← NNReal.coe_le_coe, coe_compactCadlagWeight]
    exact (inv_le_one₀
      (by positivity : (0 : ℝ) < 1 +
        (denseRunningSupremum (fun t v ↦ ‖X t v‖) T ω).toReal)).2
      (le_add_of_nonneg_right ENNReal.toReal_nonneg)
  have hνfin : IsFiniteMeasure ν := by
    apply isFiniteMeasure_withDensity
    apply ne_top_of_le_ne_top (measure_ne_top P Set.univ)
    calc
      (∫⁻ ω, (d ω : ℝ≥0∞) ∂P) ≤ ∫⁻ _ω, (1 : ℝ≥0∞) ∂P :=
        lintegral_mono hdle
      _ = P Set.univ := by simp
  have hνne : ν ≠ 0 := by
    intro hzero
    have hdae : (fun ω ↦ (d ω : ℝ≥0∞)) =ᵐ[P] 0 :=
      (withDensity_eq_zero_iff hd.coe_nnreal_ennreal.aemeasurable).mp hzero
    have hpos : ∀ᵐ ω ∂P, (d ω : ℝ≥0∞) ≠ 0 :=
      ae_of_all P fun ω ↦ ENNReal.coe_ne_zero.mpr (ne_of_gt (compactCadlagWeight_pos X T ω))
    have : ∀ᵐ _ω ∂P, False := by
      filter_upwards [hdae, hpos] with ω he hn
      exact hn he
    exact this.exists.elim fun _ h ↦ h
  let c : ℝ≥0∞ := (ν Set.univ)⁻¹
  have hνtop : ν Set.univ ≠ ∞ := measure_ne_top ν Set.univ
  have hνzero : ν Set.univ ≠ 0 := by
    exact Measure.measure_univ_ne_zero.mpr hνne
  have hcne : c ≠ 0 := ENNReal.inv_ne_zero.mpr hνtop
  have hctop : c ≠ ∞ := ENNReal.inv_ne_top.mpr hνzero
  let Q : Measure Ω := c • ν
  have hQprob : IsProbabilityMeasure Q := by
    refine ⟨?_⟩
    change c * ν Set.univ = 1
    exact ENNReal.inv_mul_cancel hνzero hνtop
  have hQP : Q ≪ P := by
    exact (Measure.smul_absolutelyContinuous.trans
      (withDensity_absolutelyContinuous P (fun ω ↦ (d ω : ℝ≥0∞))))
  have hPQ : P ≪ Q := by
    have hPν : P ≪ ν := withDensity_absolutelyContinuous'
      hd.coe_nnreal_ennreal.aemeasurable
      (ae_of_all P fun ω ↦ ENNReal.coe_ne_zero.mpr
        (ne_of_gt (compactCadlagWeight_pos X T ω)))
    exact hPν.trans (Measure.absolutelyContinuous_smul hcne)
  have hνP : ν ≤ P := by
    change P.withDensity (fun ω ↦ (d ω : ℝ≥0∞)) ≤ P
    calc
      P.withDensity (fun ω ↦ (d ω : ℝ≥0∞)) ≤ P.withDensity 1 := by
        apply withDensity_mono
        filter_upwards [] with ω
        exact hdle ω
      _ = P := withDensity_one
  have hQdom : Q ≤ c • P := by
    apply Measure.le_iff.mpr
    intro s hs
    rw [Measure.smul_apply, Measure.smul_apply, smul_eq_mul, smul_eq_mul]
    exact mul_le_mul le_rfl (Measure.le_iff.mp hνP s hs) zero_le zero_le
  let S : Ω → ℝ := fun ω ↦
    (denseRunningSupremum (fun t v ↦ ‖X t v‖) T ω).toReal
  have hSmeas : Measurable S :=
    measurable_toReal_denseRunningSupremum
      (fun t ↦ (continuous_norm.measurable.comp
        ((ha t).mono (F.le t) le_rfl))) T
  have hweightedS : Integrable (fun ω ↦ (d ω : ℝ) • S ω) P := by
    refine Integrable.of_bound
      (hd.coe_nnreal_real.mul hSmeas).aestronglyMeasurable 1 ?_
    filter_upwards [] with ω
    rw [smul_eq_mul, norm_mul, Real.norm_of_nonneg (d ω).coe_nonneg,
      Real.norm_of_nonneg ENNReal.toReal_nonneg, coe_compactCadlagWeight]
    change (1 + S ω)⁻¹ * S ω ≤ 1
    rw [inv_mul_eq_div]
    exact (div_le_one (by positivity : 0 < 1 + S ω)).2
      (le_add_of_nonneg_left zero_le_one)
  have hSintν : Integrable S ν := by
    exact (integrable_withDensity_iff_integrable_coe_smul hd).2 hweightedS
  have hSintQ : Integrable S Q := hSintν.smul_measure hctop
  refine ⟨⟨Q, hQprob, hQP, hPQ, ⟨c, hctop, hQdom⟩, hSintQ, ?_⟩⟩
  intro t ht
  have hweighted : Integrable (fun ω ↦ (d ω : ℝ) • X t ω) P := by
    refine Integrable.of_bound
      (hd.coe_nnreal_real.mul
        ((ha t).mono (F.le t) le_rfl)).aestronglyMeasurable 1 ?_
    filter_upwards [compactCadlagWeight_mul_norm_le_one_ae hc T] with ω hω
    change ‖(d ω : ℝ) * X t ω‖ ≤ 1
    rw [norm_mul, Real.norm_of_nonneg (d ω).coe_nonneg]
    exact hω t ht
  have hνint : Integrable (X t) ν := by
    exact (integrable_withDensity_iff_integrable_coe_smul hd).2 hweighted
  exact hνint.smul_measure hctop

end ProbabilityTheory
