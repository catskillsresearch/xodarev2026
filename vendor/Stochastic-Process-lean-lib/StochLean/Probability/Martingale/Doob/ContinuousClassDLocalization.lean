/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Martingale.Doob.ContinuousComparison
public import StochLean.Probability.Martingale.Convergence.ContinuousMonotoneL1
public import StochLean.Probability.Martingale.Convergence.InMeasure
public import StochLean.Probability.Process.UCP.ConsistentLocalization

/-! # Class D closure of consistent continuous local compensators

The input consists of actual local martingales and continuous increasing
compensators with proved stopped consistency. The existing UCP completion
constructs the global increasing part. Its coordinate integrability is
derived from Class D moment bounds and the native Fatou bound, not from
integrability of a sum. An actual integrable terminal envelope then bounds
all local compensators and gives the UI needed to close the global martingale.

This is the common local-to-global owner. It does not assume a global
compensator, global martingale, integrable terminal, or bounded jump sizes.
The original process need not separately be declared a supermartingale.
The pre-localizer may be nonmonotone and may take infinite values.
-/

@[expose] public section

open ProbabilityTheory Filter
open scoped NNReal ENNReal Topology

namespace MeasureTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}

private theorem eLpNorm_one_eq_ofReal_integral_of_ae_nonneg {f : Ω → ℝ}
    (hi : Integrable f P) (hn : ∀ᵐ ω ∂P, 0 ≤ f ω) :
    eLpNorm f 1 P = ENNReal.ofReal (∫ ω, f ω ∂P) := by
  rw [eLpNorm_one_eq_lintegral_enorm, ← ofReal_integral_norm_eq_lintegral_enorm hi]
  congr 1
  exact integral_congr_ae (hn.mono fun _ hω ↦ Real.norm_of_nonneg hω)

variable [IsProbabilityMeasure P] {F : Filtration ℝ≥0 mΩ}
  {X : ℝ≥0 → Ω → ℝ} {τ : ℕ → Ω → WithTop ℝ≥0} {B : ℕ → ℝ≥0 → Ω → ℝ}

/-- Consistent actual continuous local compensators of an adapted Class D
process produce an exact-zero continuous global compensator, a true UI
martingale, and an actual whole-half-line integrable compensator terminal. -/
theorem exists_continuous_doob_decomposition_of_consistent_classD_localization
    (hXa : Adapted F X) (hXD : IsClassD X F P) (hF : F.IsUsual P)
    (hc : HasCadlagPaths X P) (h0 : X 0 =ᵐ[P] 0)
    (hτ : IsPreLocalizingSequence F τ P)
    (hBa : ∀ n, Adapted F (B n)) (hBc : ∀ n ω, Continuous (B n · ω))
    (hB0 : ∀ n, B n 0 = 0) (hBm : ∀ n, HasMonotonePaths (B n) P)
    (hMn : ∀ n, Martingale (stoppedProcess X (τ n) + B n) F P)
    (hcons : ∀ n m, n ≤ m → Indistinguishable (stoppedProcess (B m) (τ n)) (B n) P) :
    ∃ (A : ℝ≥0 → Ω → ℝ) (Z : Ω → ℝ),
      Adapted F A ∧ IsStronglyPredictable F A ∧ (∀ ω, Continuous (A · ω)) ∧
      A 0 = 0 ∧ HasMonotonePaths A P ∧ HasFiniteVariationPaths A P ∧
      IsClassD A F P ∧ Martingale (X + A) F P ∧ HasCadlagPaths (X + A) P ∧
      UniformIntegrable (X + A) 1 P ∧ Integrable Z P ∧
      (∀ᵐ ω ∂P, ∀ t, 0 ≤ A t ω ∧ A t ω ≤ Z ω) ∧
      (∀ᵐ ω ∂P, Tendsto (fun t : ℝ≥0 ↦ A t ω) atTop (𝓝 (Z ω))) ∧
      Tendsto (fun t : ℝ≥0 ↦ eLpNorm (A t - Z) 1 P) atTop (𝓝 0) := by
  let S : ℕ → ℝ≥0 → Ω → ℝ := fun n ↦ stoppedProcess X (τ n)
  obtain ⟨Y, hYa, hYc, hBY, hYrec, hYm, _, hY0, _, _⟩ :=
    hτ.exists_continuous_monotone_limit_of_stopped_consistency hF hBa hBc hcons hBm
      (fun n ↦ Eventually.of_forall fun ω ↦ congrFun (hB0 n) ω)
  let A : ℝ≥0 → Ω → ℝ := fun t ω ↦ Y t ω - Y 0 ω
  have hAa : Adapted F A := fun t ↦
    (hYa t).sub ((hYa 0).mono (F.mono bot_le) le_rfl)
  have hAc (ω : Ω) : Continuous (A · ω) := (hYc ω).sub continuous_const
  have hA0 : A 0 = 0 := funext fun _ ↦ sub_self _
  have heYA : Indistinguishable Y A P := by
    filter_upwards [hY0] with ω hω t
    change Y t ω = Y t ω - Y 0 ω
    rw [hω]
    exact (sub_zero _).symm
  have hAm : HasMonotonePaths A P := hYm.congr heYA
  have hAn : ∀ᵐ ω ∂P, ∀ t, 0 ≤ A t ω := by
    filter_upwards [hAm] with ω hω t
    have hz := congrFun hA0 ω
    have h := hω (bot_le : (0 : ℝ≥0) ≤ t)
    change A 0 ω ≤ A t ω at h
    simpa only [hz, Pi.zero_apply] using h
  have hBA : TendstoUCP P B atTop A := hBY.congr_right heYA
  have hrec (n : ℕ) : Indistinguishable (stoppedProcess A (τ n)) (B n) P :=
    ((heYA.stoppedProcess (τ n)).symm).trans (hYrec n)
  let σ (n : ℕ) (t : ℝ≥0) : FiniteStoppingTime F :=
    FiniteStoppingTime.truncate (hτ.isStoppingTime n) t
  have hSi (n : ℕ) (t : ℝ≥0) : Integrable (S n t) P :=
    hXD.integrable_finiteStoppingTime_value (σ n t)
  have hBi (n : ℕ) (t : ℝ≥0) : Integrable (B n t) P := by
    have he : B n t = (S n + B n) t - S n t := by
      funext ω
      simp only [Pi.sub_apply, Pi.add_apply]
      ring
    rw [he]
    exact ((hMn n).integrable t).sub (hSi n t)
  obtain ⟨C, hC⟩ := hXD.2.2
  have hSnorm (n : ℕ) (t : ℝ≥0) : (∫ ω, ‖S n t ω‖ ∂P) ≤ C := by
    have h := hC (σ n t)
    change eLpNorm (S n t) 1 P ≤ (C : ℝ≥0∞) at h
    rw [eLpNorm_one_eq_lintegral_enorm,
      ← ofReal_integral_norm_eq_lintegral_enorm (hSi n t)] at h
    exact ENNReal.ofReal_le_coe.mp h
  have hBn (n : ℕ) : ∀ᵐ ω ∂P, ∀ t, 0 ≤ B n t ω := by
    filter_upwards [hBm n] with ω hω t
    have hz := congrFun (hB0 n) ω
    have h := hω (bot_le : (0 : ℝ≥0) ≤ t)
    change B n 0 ω ≤ B n t ω at h
    simpa only [hz, Pi.zero_apply] using h
  have hEB (n : ℕ) (t : ℝ≥0) : (∫ ω, B n t ω ∂P) ≤ C := by
    have hS0 : S n 0 =ᵐ[P] 0 := by
      filter_upwards [h0] with ω hω
      exact (stoppedProcess_eq_of_le (u := X) (τ := τ n)
        (i := (0 : ℝ≥0)) (ω := ω) bot_le).trans hω
    have h := (hMn n).integral_add_compensator_eq
      (Eventually.of_forall fun ω ↦ congrFun (hB0 n) ω) t (hSi n t) (hBi n t)
    rw [integral_congr_ae hS0] at h
    simp only [Pi.zero_apply, integral_zero, zero_sub] at h
    rw [h]
    have hnorm : |∫ ω, S n t ω ∂P| ≤ ∫ ω, ‖S n t ω‖ ∂P := by
      simpa only [Real.norm_eq_abs] using norm_integral_le_integral_norm (S n t)
    exact ((neg_le_abs _).trans hnorm).trans (hSnorm n t)
  have hBnorm (n : ℕ) (t : ℝ≥0) : eLpNorm (B n t) 1 P ≤ (C : ℝ≥0∞) := by
    rw [eLpNorm_one_eq_ofReal_integral_of_ae_nonneg (hBi n t)
      ((hBn n).mono fun _ hω ↦ hω t)]
    exact ENNReal.ofReal_le_coe.mpr (hEB n t)
  have hAnorm (t : ℝ≥0) : eLpNorm (A t) 1 P ≤ (C : ℝ≥0∞) :=
    eLpNorm_le_of_tendstoInMeasure (Eventually.of_forall fun n ↦ hBnorm n t)
      (hBA.fixedTime t) (fun n ↦ (hBi n t).aestronglyMeasurable)
  have hAi (t : ℝ≥0) : Integrable (A t) P :=
    memLp_one_iff_integrable.mp
      ⟨((hAa t).mono (F.le t) le_rfl).aestronglyMeasurable,
        (hAnorm t).trans_lt ENNReal.coe_lt_top⟩
  have hEA (t : ℝ≥0) : (∫ ω, A t ω ∂P) ≤ C := by
    have h := hAnorm t
    rw [eLpNorm_one_eq_ofReal_integral_of_ae_nonneg (hAi t)
      (hAn.mono fun _ hω ↦ hω t)] at h
    exact ENNReal.ofReal_le_coe.mp h
  obtain ⟨Z, hiZ, _, hZbound, hZlim, _, hZL1⟩ :=
    hAm.exists_integrable_terminal_of_integral_bounded hAa hAi hAn hEA
  have hrA : HasRightContinuousPaths A P :=
    Eventually.of_forall fun ω ↦ IsContinuousPath.isRightContinuousPath (hAc ω)
  have hAD : IsClassD A F P :=
    hAm.isClassD_of_nonneg_of_integral_bounded hAa hAi hAn hEA hF hrA
  have huiB (t : ℝ≥0) : UniformIntegrable (fun n ↦ B n t) 1 P := by
    apply (uniformIntegrable_const le_rfl ENNReal.one_ne_top
      (memLp_one_iff_integrable.mpr hiZ)).mono_norm
      (fun n ↦ (hBi n t).aestronglyMeasurable)
    intro n
    filter_upwards [hrec n, hZbound] with ω he hω
    rw [← he t]
    change ‖A (min (t : WithTop ℝ≥0) (τ n ω)).untopA ω‖ ≤ ‖Z ω‖
    have hv := hω (min (t : WithTop ℝ≥0) (τ n ω)).untopA
    rw [Real.norm_of_nonneg hv.1, Real.norm_of_nonneg (hv.1.trans hv.2)]
    exact hv.2
  have huiM (t : ℝ≥0) : UniformIntegrable (fun n ↦ (S n + B n) t) 1 P :=
    (hXD.uniformIntegrable_finiteStoppingTime (fun n ↦ σ n t)).add (huiB t) le_rfl
  have hlM (t : ℝ≥0) : ∀ᵐ ω ∂P,
      Tendsto (fun n ↦ (S n + B n) t ω) atTop (𝓝 ((X + A) t ω)) := by
    filter_upwards [ae_all_iff.mpr hrec, hτ.tendsto_top] with ω hω htω
    apply tendsto_const_nhds.congr'
    filter_upwards [htω.eventually (Ioi_mem_nhds (WithTop.coe_lt_top t))] with n hn
    have heB := hω n t
    rw [stoppedProcess_eq_of_le hn.le] at heB
    change X t ω + A t ω = stoppedProcess X (τ n) t ω + B n t ω
    rw [stoppedProcess_eq_of_le hn.le, heB]
  have hM : Martingale (X + A) F P :=
    martingale_of_tendstoInMeasure_uniformIntegrable hMn
      (hXa.stronglyAdapted.add hAa.stronglyAdapted) huiM
      (fun t ↦ tendstoInMeasure_of_tendsto_ae
        (fun n ↦ ((hMn n).integrable t).aestronglyMeasurable) (hlM t))
  have hAp : IsStronglyPredictable F A :=
    hAa.isStronglyPredictable_of_leftContinuous (fun ω t ↦ (hAc ω).continuousWithinAt)
  have hcA : HasCadlagPaths A P :=
    Eventually.of_forall fun ω ↦ IsContinuousPath.isCadlagPath (hAc ω)
  exact ⟨A, Z, hAa, hAp, hAc, hA0, hAm, hAm.hasFiniteVariationPaths, hAD, hM,
    hc.add hcA, (hXD.add hAD).uniformIntegrable, hiZ, hZbound, hZlim, hZL1⟩

end MeasureTheory
