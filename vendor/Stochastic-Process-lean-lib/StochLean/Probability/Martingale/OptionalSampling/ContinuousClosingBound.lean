/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Conditional.StoppingBounds
public import StochLean.ForMathlib.MeasureTheory.ConditionalLowerBound
public import StochLean.Probability.Martingale.OptionalSampling.ContinuousOneSidedUsual

/-! # Lower closing bounds at bounded stopping times

Protter's supermartingale closure is a conditional lower bound, not an
assumed path limit or equality. The coordinatewise lower bound passes through
the existing upper approximations by their proved L1 convergence. No regular
version of the conditional-expectation process is assumed or constructed.
-/

@[expose] public section

open ProbabilityTheory Filter
open scoped NNReal ENNReal Topology

namespace MeasureTheory.Supermartingale

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsFiniteMeasure P]
  {F : Filtration ℝ≥0 mΩ} {X : ℝ≥0 → Ω → ℝ} {Y : Ω → ℝ}

theorem condExp_closing_le_finiteStoppingTime_of_progressive
    (hX : Supermartingale X F P) (hp : IsStronglyProgressive F X)
    (hr : HasRightContinuousPaths X P) (hY : Integrable Y P)
    (hclose : ∀ t, P[Y | F t] ≤ᵐ[P] X t) (τ : FiniteStoppingTime F)
    {T : ℝ≥0} (hb : ∀ ω, τ ω ≤ T) :
    P[Y | τ.measurableSpace] ≤ᵐ[P] (fun ω ↦ X (τ ω) ω) := by
  have hi := hX.integrable_finiteStoppingTime_value τ hb hr
  have hm := (measurable_stoppedValue hp τ.isStoppingTime).stronglyMeasurable
  have hset (A : Set Ω) (hA : MeasurableSet[τ.measurableSpace] A) :
      (∫ ω in A, Y ω ∂P) ≤ ∫ ω in A, X (τ ω) ω ∂P := by
    have hlim := tendsto_setIntegral_of_L1' (fun ω ↦ X (τ ω) ω) hi.aestronglyMeasurable
      (Eventually.of_forall fun n ↦ hX.integrable_upperApprox_value τ T (2 ^ n - 1))
      (hX.tendsto_eLpNorm_dyadic_upperApprox_value τ hb hr) A
    apply le_of_tendsto_of_tendsto' tendsto_const_nhds hlim
    intro n
    let S := τ.upperApprox T (2 ^ n - 1)
    have hc : (Set.range S.withTop).Countable := by
      apply ((τ.countable_range_upperApprox T (2 ^ n - 1)).image
        (fun t : ℝ≥0 ↦ (t : WithTop ℝ≥0))).mono
      rintro t ⟨ω, rfl⟩
      exact ⟨S ω, ⟨ω, rfl⟩, rfl⟩
    have hbound := condExp_le_stoppedValue_of_countable_range hclose S.isStoppingTime
      S.withTop_ne_top hc
    have hAn : MeasurableSet[S.measurableSpace] A :=
      τ.isStoppingTime.measurableSpace_mono S.isStoppingTime
        (fun ω ↦ WithTop.coe_le_coe.mpr (τ.le_upperApprox hb _ ω)) A hA
    calc
      _ = ∫ ω in A, P[Y | S.measurableSpace] ω ∂P :=
        (setIntegral_condExp S.measurableSpace_le hY hAn).symm
      _ ≤ _ := setIntegral_mono_ae integrable_condExp.integrableOn
        (hX.integrable_upperApprox_value τ T _).integrableOn hbound
  have hn := ae_le_condExp_of_forall_setIntegral_le τ.measurableSpace_le hi.neg hY.neg
    hm.neg (fun A hA ↦ by
      simp only [Pi.neg_apply, integral_neg]
      exact neg_le_neg (hset A hA))
  filter_upwards [hn, condExp_neg Y τ.measurableSpace] with ω hnω heω
  rw [heω] at hnω
  exact neg_le_neg_iff.mp hnω

theorem condExp_closing_le_finiteStoppingTime
    (hX : Supermartingale X F P) (hF : F.IsUsual P)
    (hr : HasRightContinuousPaths X P) (hY : Integrable Y P)
    (hclose : ∀ t, P[Y | F t] ≤ᵐ[P] X t) (τ : FiniteStoppingTime F)
    {T : ℝ≥0} (hb : ∀ ω, τ ω ≤ T) :
    P[Y | τ.measurableSpace] ≤ᵐ[P] (fun ω ↦ X (τ ω) ω) := by
  obtain ⟨Z, hmod, hp, hc⟩ :=
    hX.stronglyAdapted.exists_isStronglyProgressive_modification_of_hasRightContinuousPaths hF hr
  have hZ := hX.congr hp.stronglyAdapted hmod
  have hrc : HasRightContinuousPaths Z P := Eventually.of_forall hc
  have he := hmod.indistinguishable_of_rightContinuous hr hrc
  have hcloseZ (t) : P[Y | F t] ≤ᵐ[P] Z t := (hclose t).trans_eq (hmod t)
  have h := hZ.condExp_closing_le_finiteStoppingTime_of_progressive hp hrc hY hcloseZ τ hb
  filter_upwards [h, he] with ω hω heω
  rwa [← heω (τ ω)] at hω

theorem condExp_closing_le_stoppedValue_of_bounded
    (hX : Supermartingale X F P) (hF : F.IsUsual P)
    (hr : HasRightContinuousPaths X P) (hY : Integrable Y P)
    (hclose : ∀ t, P[Y | F t] ≤ᵐ[P] X t)
    {τ : Ω → WithTop ℝ≥0} (hτ : IsStoppingTime F τ)
    {T : ℝ≥0} (hb : ∀ ω, τ ω ≤ T) :
    P[Y | hτ.measurableSpace] ≤ᵐ[P] stoppedValue X τ := by
  have hf (ω) : τ ω ≠ ⊤ := ne_top_of_le_ne_top WithTop.coe_ne_top (hb ω)
  let S := FiniteStoppingTime.ofNotTop hτ hf
  have he : S.withTop = τ := FiniteStoppingTime.withTop_ofNotTop hτ hf
  have hfield : S.measurableSpace = hτ.measurableSpace :=
    FiniteStoppingTime.measurableSpace_ofNotTop hτ hf
  have hST (ω) : S ω ≤ T := by
    apply WithTop.coe_le_coe.mp
    change S.withTop ω ≤ (T : WithTop ℝ≥0)
    rw [he]
    exact hb ω
  have h := hX.condExp_closing_le_finiteStoppingTime hF hr hY hclose S hST
  simpa only [← FiniteStoppingTime.stoppedValue_eq, he, hfield] using h

/-- The bound is independent of the deterministic stopping horizon. It is
an L1 bound, not uniform integrability of all bounded stopping values. -/
theorem integral_norm_finiteStoppingTime_value_le_of_closing
    (hX : Supermartingale X F P) (hF : F.IsUsual P)
    (hr : HasRightContinuousPaths X P) (hY : Integrable Y P)
    (hclose : ∀ t, P[Y | F t] ≤ᵐ[P] X t) (τ : FiniteStoppingTime F)
    {T : ℝ≥0} (hb : ∀ ω, τ ω ≤ T) :
    (∫ ω, ‖X (τ ω) ω‖ ∂P) ≤ (∫ ω, X 0 ω ∂P) + 2 * (∫ ω, ‖Y ω‖ ∂P) := by
  have hi := hX.integrable_finiteStoppingTime_value τ hb hr
  have hc := hX.condExp_closing_le_finiteStoppingTime hF hr hY hclose τ hb
  have hs := hX.condExp_finiteStoppingTime_value_ae_le_of_le hF hr
    (FiniteStoppingTime.const F 0) τ (fun _ ↦ bot_le) hb
  have he := integral_mono_ae integrable_condExp (hX.integrable 0) hs
  rw [integral_condExp (FiniteStoppingTime.const F 0).measurableSpace_le] at he
  exact (hi.integral_norm_le_of_condExp_le hc).trans (add_le_add he le_rfl)

end MeasureTheory.Supermartingale
