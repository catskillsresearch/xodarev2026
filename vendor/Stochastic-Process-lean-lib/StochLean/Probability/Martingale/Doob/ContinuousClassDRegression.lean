/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Martingale.Doob.ContinuousClassD
public import StochLean.Probability.Process.Stopping.OptionalValue

/-! # Actual Doob construction for an integrable random-amplitude ramp

The amplitude is nonnegative, integrable and measurable at time zero.
No deterministic bound on that amplitude or on the process is assumed.
The full Class D theorem constructs a compensator; continuous FV
uniqueness then identifies it with the increasing random-amplitude ramp.
-/

@[expose] public section

open MeasureTheory Filter
open scoped NNReal ENNReal

namespace ProbabilityTheory.ContinuousClassDRegression

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
  {F : Filtration ℝ≥0 mΩ} {Z : Ω → ℝ}

/-- The genuinely constructed compensator works for every integrable
nonnegative initial-measurable amplitude, with no uniform bound supplied. -/
theorem exists_actual_compensator_integrable_amplitude (hF : F.IsUsual P)
    (hmZ : StronglyMeasurable[F 0] Z) (hiZ : Integrable Z P)
    (hnZ : ∀ᵐ ω ∂P, 0 ≤ Z ω) :
    let X : ℝ≥0 → Ω → ℝ := fun t ω ↦ -Z ω * min (t : ℝ) 1
    let B : ℝ≥0 → Ω → ℝ := fun t ω ↦ Z ω * min (t : ℝ) 1
    ∃ A : ℝ≥0 → Ω → ℝ,
      Adapted F A ∧ IsStronglyPredictable F A ∧ (∀ ω, Continuous (A · ω)) ∧
      A 0 = 0 ∧ IsClassD A F P ∧ Martingale (X + A) F P ∧
      Indistinguishable A B P := by
  intro X B
  have hXa : StronglyAdapted F X := by
    intro t
    let : MeasurableSpace Ω := F t
    exact ((hmZ.mono (F.mono bot_le)).neg).mul stronglyMeasurable_const
  have hXc (ω : Ω) : Continuous (X · ω) :=
    continuous_const.mul (NNReal.continuous_coe.min continuous_const)
  have hBc (ω : Ω) : Continuous (B · ω) :=
    continuous_const.mul (NNReal.continuous_coe.min continuous_const)
  have hXcad (ω : Ω) : IsCadlagPath (X · ω) := IsContinuousPath.isCadlagPath (hXc ω)
  have hbound (ω : Ω) (t : ℝ≥0) : ‖X t ω‖ ≤ ‖Z ω‖ := by
    change ‖-Z ω * min (t : ℝ) 1‖ ≤ ‖Z ω‖
    rw [norm_mul, norm_neg, Real.norm_of_nonneg (le_min t.coe_nonneg zero_le_one)]
    exact mul_le_of_le_one_right (norm_nonneg _) (min_le_right _ _)
  have hXD : IsClassD X F P := by
    have ho := hXa.adapted.isStronglyOptional_of_cadlag hXcad
    apply (isClassD_const (F := F) hiZ).mono_norm
    · intro σ
      exact ((ho.stronglyMeasurable_finiteStoppingTime σ).mono
        σ.measurableSpace_le).aestronglyMeasurable
    · intro σ
      exact Eventually.of_forall fun ω ↦ hbound ω (σ ω)
  have hX : Supermartingale X F P := by
    refine ⟨hXa, ?_, hXD.integrable⟩
    intro s t hst
    have hle : X t ≤ᵐ[P] X s := by
      filter_upwards [hnZ] with ω hω
      exact mul_le_mul_of_nonpos_left
        (min_le_min (NNReal.coe_le_coe.mpr hst) le_rfl) (neg_nonpos.mpr hω)
    have he := condExp_mono (hXD.integrable t) (hXD.integrable s) hle (m := F s)
    rwa [condExp_of_stronglyMeasurable (F.le s) (hXa s) (hXD.integrable s)] at he
  have h0X : X 0 =ᵐ[P] 0 := Eventually.of_forall fun ω ↦ by simp only [X]; norm_num
  obtain ⟨A, _, ha, hp, hc, hz, _, hv, hD, hM, _, _, _, _, _, _⟩ :=
    hX.exists_continuous_doob_decomposition_of_classD hXD hF
      (Eventually.of_forall hXcad)
      (HasContinuousPaths.hasTotallyInaccessibleJumps (Eventually.of_forall hXc) F)
      h0X
  have hB0 : B 0 =ᵐ[P] 0 := Eventually.of_forall fun ω ↦ by simp only [B]; norm_num
  have hBm : HasMonotonePaths B P := by
    filter_upwards [hnZ] with ω hω
    intro s t hst
    exact mul_le_mul_of_nonneg_left
      (min_le_min (NNReal.coe_le_coe.mpr hst) le_rfl) hω
  have hMB : Martingale (X + B) F P := by
    convert martingale_const F P (0 : ℝ) using 1
    funext t ω
    change -Z ω * min (t : ℝ) 1 + Z ω * min (t : ℝ) 1 = 0
    ring
  have hid := indistinguishable_of_continuous_finiteVariation_martingale_add_zero hF hM hMB
    (Eventually.of_forall hc) (Eventually.of_forall hBc) hv hBm.hasFiniteVariationPaths
    (Eventually.of_forall fun ω ↦ congrFun hz ω) hB0
  exact ⟨A, ha, hp, hc, hz, hD, hM, hid⟩

end ProbabilityTheory.ContinuousClassDRegression
