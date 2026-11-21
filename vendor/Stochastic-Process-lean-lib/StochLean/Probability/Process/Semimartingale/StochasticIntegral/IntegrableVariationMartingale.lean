/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.Semimartingale.LocalMartingale
public import StochLean.Probability.Process.Semimartingale.StochasticIntegral.IntegrableVariation
public import StochLean.Probability.Process.Semimartingale.SimplePredictable.BoundedDensity
public import StochLean.Probability.Process.Semimartingale.SimplePredictable.Martingale
public import StochLean.Probability.Process.Semimartingale.SimplePredictable.VariationBound
public import StochLean.Probability.Process.LocalMartingale.Bounded
public import StochLean.Probability.Martingale.Convergence.InMeasure

/-! # Bounded integration against an integrable-variation local martingale

The actual global variation and the integrable initial value give a common
integrable envelope for the source local martingale, so it is a true UI
martingale. Bounded simple approximations have true martingale integrals and
share the original variation envelope. Their UCP limit is therefore a true
martingale by coordinatewise uniform-integrability closure.

The selected integral itself has actual integrable variation by its proved
Stieltjes agreement. Its initial value is the original product, proved
integrable before invoking Class D or the martingale limit theorem. Thus the
conclusion is UI without a source bound, L2 hypothesis, continuous paths, or
an assumed integral martingale property. Extended variation is finite before
any comparison using its real conversion.
-/

@[expose] public section

open MeasureTheory Filter Set
open scoped NNReal ENNReal

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
  {F : Filtration ℝ≥0 mΩ} {A H : ℝ≥0 → Ω → ℝ}

/-- A bounded adapted caglad integrand preserves true UI martingality for an
actual integrable-variation local martingale with integrable initial value.
The conclusion concerns the existing stochastic integral, including its
time-zero product, not a new integral or a supplied limit. -/
theorem IsLocalMartingale.isUIMartingale_stochasticIntegral_of_integrableVariation
    (hA : IsLocalMartingale A F P) (hF : F.IsUsual P)
    (hv : HasIntegrableVariation A P) (hi0 : Integrable (A 0) P)
    (ha : Adapted F H) (hr : HasCagladPaths H P)
    {C : ℝ} (hC : 0 ≤ C) (hb : ∀ᵐ ω ∂P, ∀ t, ‖H t ω‖ ≤ C) :
    IsUIMartingale ((hA.isSemimartingale hF).stochasticIntegral hF ha hr) F P := by
  let hSM := hA.isSemimartingale hF
  let J := hSM.stochasticIntegral hF ha hr
  let G : Ω → ℝ := fun ω ↦ ‖A 0 ω‖ + (eVariationOn (A · ω) univ).toReal
  have hiG : Integrable G P := hi0.norm.add hv.integrable_eVariationOn_toReal
  have hboundA : ∀ᵐ ω ∂P, ∀ t, ‖A t ω‖ ≤ G ω := by
    filter_upwards [hv.ae_forall_norm_sub_le] with ω hω t
    calc
      ‖A t ω‖ ≤ ‖A t ω - A 0 ω‖ + ‖A 0 ω‖ := by
        simpa only [sub_add_cancel] using norm_add_le (A t ω - A 0 ω) (A 0 ω)
      _ ≤ (eVariationOn (A · ω) univ).toReal + ‖A 0 ω‖ :=
        add_le_add (hω 0 t) le_rfl
      _ = G ω := add_comm _ _
  have hM : Martingale A F P :=
    (hA.isUIMartingale_of_integrable_envelope hiG hboundA).1
  have hJa : Adapted F J := hSM.adapted_stochasticIntegral hF ha hr
  have hJc : HasCadlagPaths J P := hSM.hasCadlagPaths_stochasticIntegral hF ha hr
  have hvJ : HasIntegrableVariation J P :=
    hSM.hasIntegrableVariation_stochasticIntegral hF hv ha hr hC
      (hb.mono fun _ hω t _ ↦ hω t)
  have hiProduct : Integrable (fun ω ↦ H 0 ω * A 0 ω) P :=
    hi0.bdd_smul C ((ha 0).mono (F.le 0) le_rfl).aestronglyMeasurable
      (hb.mono fun _ hω ↦ hω 0)
  have hiJ0 : Integrable (J 0) P :=
    hiProduct.congr (hSM.stochasticIntegral_zero_ae hF ha hr).symm
  have hDJ : IsClassD J F P := hvJ.isClassD hJa hF hJc hiJ0
  let Cnn : ℝ≥0 := NNReal.mk C hC
  obtain ⟨S, hS, hSb, huS⟩ := exists_bounded_simplePredictable_tendstoUCP ha hF hr Cnn hb
  have huJ := hSM.tendstoUCP_stochasticIntegral_of_simple hF ha hr hS huS
  have hboundS (n : ℕ) : ∀ᵐ ω ∂P, ∀ t,
      ‖(hS n).elementaryIntegralProcess A t ω‖ ≤ C * G ω := by
    filter_upwards [hv.hasFiniteTotalVariationPaths] with ω hω t
    rw [(hS n).elementaryIntegralProcess_eq (hS n).choose (hS n).choose_spec A]
    have hcompact := hω.mono (subset_univ (Icc 0 t))
    have hmin := (hS n).choose.norm_integral_min_const_le_variation hC
      (by simpa only [Cnn, NNReal.coe_mk, (hS n).choose_spec] using hSb n) ω t hcompact
    apply hmin.trans
    exact mul_le_mul_of_nonneg_left
      (add_le_add le_rfl (ENNReal.toReal_mono hω
        (eVariationOn.mono _ (subset_univ (Icc 0 t))))) hC
  have hiBound : Integrable (fun ω ↦ C * G ω) P := hiG.const_mul C
  have hiS (n : ℕ) (t : ℝ≥0) : Integrable ((hS n).elementaryIntegralProcess A t) P :=
    hiBound.mono'
      (((hS n).adapted_elementaryIntegralProcess hA.1 hF
        hA.2.1.hasRightContinuousPaths t).mono (F.le t) le_rfl).aestronglyMeasurable
      ((hboundS n).mono fun _ hω ↦ hω t)
  have hMS (n : ℕ) : Martingale ((hS n).elementaryIntegralProcess A) F P :=
    (hS n).martingale_elementaryIntegralProcess hM hF hA.2.1.hasRightContinuousPaths
      Cnn (hSb n)
  have hUI (t : ℝ≥0) :
      UniformIntegrable (fun n ↦ (hS n).elementaryIntegralProcess A t) 1 P := by
    have hconst : UniformIntegrable (fun _ : ℕ ↦ fun ω ↦ C * G ω) 1 P :=
      uniformIntegrable_const le_rfl (by simp) (memLp_one_iff_integrable.mpr hiBound)
    apply hconst.mono_norm (fun n ↦ (hiS n t).aestronglyMeasurable)
    intro n
    filter_upwards [hboundS n] with ω hω
    exact (hω t).trans (le_abs_self _)
  exact ⟨martingale_of_tendstoInMeasure_uniformIntegrable hMS hJa.stronglyAdapted hUI
    huJ.fixedTime, hDJ.uniformIntegrable⟩

end ProbabilityTheory
