/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Martingale.Doob.SingleJumpComparison
public import StochLean.Probability.Martingale.Convergence.ContinuousMonotoneL1
public import StochLean.Probability.Martingale.Convergence.ContinuousL1Limit
public import StochLean.Probability.Martingale.Convergence.InMeasure
public import StochLean.Probability.Process.UCP.CagladContinuousLimit
public import StochLean.Probability.Process.UCP.MonotoneLimit

/-! # A continuous compensator for an integrable totally inaccessible single jump

The bounded clipped single-jump theorem constructs the approximants. Actual
compensator comparison makes them increasing in the clipping level and
UCP-Cauchy. Existing continuous UCP completeness gives their limit, whose
initial value is normalized exactly by an indistinguishable adapted change.

The true approximating martingales bound the compensator expectations by
the mean amplitude. At each fixed time, discrete monotone L1 convergence
therefore gives uniform integrability across clipping levels. This closes
the limiting martingale without first assuming a terminal compensator.
Only afterwards does the increasing-process terminal theorem construct an
actual integrable envelope on the whole half-line and prove Class D.

The lifetime may be infinite and the coefficient need not be bounded.
Neither a compensator, a terminal variable, nor a convergence or UI
certificate is required in the final existence theorem's hypotheses.
-/

@[expose] public section

open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
  {F : Filtration ℝ≥0 mΩ} {τ : Ω → WithTop ℝ≥0} {C : Ω → ℝ}

local notation "J" => (fun (n : ℕ) (t : ℝ≥0) ↦
  Set.indicator (Set.ofPred (fun ω ↦ τ ω ≤ (t : WithTop ℝ≥0)))
    (fun ω ↦ -min (C ω) (n : ℝ)))

local notation "X" => (fun t : ℝ≥0 ↦
  Set.indicator (Set.ofPred (fun ω ↦ τ ω ≤ (t : WithTop ℝ≥0))) (fun ω ↦ -C ω))

private theorem integral_clipped_compensator_le
    (hτ : IsTotallyInaccessibleStoppingTime F τ P)
    (hm : StronglyMeasurable[hτ.1.measurableSpace] C) (hi : Integrable C P)
    (hn : ∀ᵐ ω ∂P, 0 ≤ C ω) {B : ℕ → ℝ≥0 → Ω → ℝ}
    (hB0 : ∀ n, B n 0 =ᵐ[P] 0) (hMB : ∀ n, Martingale (J n + B n) F P)
    (n : ℕ) (t : ℝ≥0) : (∫ ω, B n t ω ∂P) ≤ ∫ ω, C ω ∂P := by
  have hiJ := (supermartingale_indicator_stoppingTime_le_neg_min hτ.1 hm hi hn
    (Nat.cast_nonneg n)).integrable t
  have hiB := hτ.integrable_continuous_compensator_neg_min hm hi hn hMB n t
  have he := (hMB n).integral_add_compensator_eq (hB0 n) t hiJ hiB
  rw [integral_congr_ae (hτ.indicator_initial_ae_eq_zero
    (fun ω ↦ -min (C ω) (n : ℝ)))] at he
  simp only [Pi.zero_apply, integral_zero, zero_sub] at he
  rw [he, ← integral_neg]
  apply integral_mono_ae hiJ.neg hi
  filter_upwards [hn] with ω hω
  change -(J n t ω) ≤ C ω
  by_cases ht : τ ω ≤ (t : WithTop ℝ≥0)
  · simp only [indicator_apply, mem_ofPred_eq, if_pos ht, neg_neg]
    exact min_le_left _ _
  · simpa only [indicator_apply, mem_ofPred_eq, if_neg ht, neg_zero] using hω

/-- The actual negative single jump has a continuous predictable increasing
compensator. Both its integrable terminal envelope and the martingale's
actual whole-half-line closing limit are constructed. -/
theorem IsTotallyInaccessibleStoppingTime.exists_continuous_compensator_neg
    (hτ : IsTotallyInaccessibleStoppingTime F τ P)
    (hF : F.IsUsual P) (hm : StronglyMeasurable[hτ.1.measurableSpace] C)
    (hi : Integrable C P) (hn : ∀ᵐ ω ∂P, 0 ≤ C ω) :
    ∃ (A : ℝ≥0 → Ω → ℝ) (Z L : Ω → ℝ),
      Adapted F A ∧ IsStronglyPredictable F A ∧ (∀ ω, Continuous (A · ω)) ∧
      A 0 = 0 ∧ HasMonotonePaths A P ∧ HasFiniteVariationPaths A P ∧ IsClassD A F P ∧
      Integrable Z P ∧ (∫ ω, Z ω ∂P) ≤ ∫ ω, C ω ∂P ∧
      (∀ᵐ ω ∂P, ∀ t, 0 ≤ A t ω ∧ A t ω ≤ Z ω) ∧
      (∀ᵐ ω ∂P, Tendsto (fun t : ℝ≥0 ↦ A t ω) atTop (𝓝 (Z ω))) ∧
      Tendsto (fun t : ℝ≥0 ↦ eLpNorm (A t - Z) 1 P) atTop (𝓝 0) ∧
      Martingale (X + A) F P ∧ HasCadlagPaths (X + A) P ∧
      IsClassD (X + A) F P ∧ UniformIntegrable (X + A) 1 P ∧
      Integrable L P ∧
      (∀ᵐ ω ∂P, Tendsto (fun t : ℝ≥0 ↦ (X + A) t ω) atTop (𝓝 (L ω))) ∧
      Tendsto (fun t : ℝ≥0 ↦ eLpNorm ((X + A) t - L) 1 P) atTop (𝓝 0) ∧
      ∀ t, (X + A) t =ᵐ[P] P[L | F t] := by
  classical
  have hex (n : ℕ) : ∃ B : ℝ≥0 → Ω → ℝ,
      Adapted F B ∧ (∀ ω, Continuous (B · ω)) ∧ B 0 = 0 ∧
      HasMonotonePaths B P ∧ HasFiniteVariationPaths B P ∧ Martingale (J n + B) F P := by
    obtain ⟨B, _, hBa, _, hBc, hB0, hBm, hBv, _, _, hBM, _, _, _, _⟩ :=
      hτ.exists_continuous_compensator_neg_min hF hm hi hn (Nat.cast_nonneg n)
    exact ⟨B, hBa, hBc, hB0, hBm, hBv, hBM⟩
  choose B hBa hBc hBzero hBm hBv hBM using hex
  have hB0 (n : ℕ) : B n 0 =ᵐ[P] 0 :=
    Eventually.of_forall fun ω ↦ congrFun (hBzero n) ω
  have hBcont (n : ℕ) : HasContinuousPaths (B n) P := Eventually.of_forall (hBc n)
  have hBnonneg (n : ℕ) : ∀ᵐ ω ∂P, ∀ t : ℝ≥0, 0 ≤ B n t ω := by
    filter_upwards [hBm n, hB0 n] with ω hω h0ω t
    have he := hω (bot_le : (0 : ℝ≥0) ≤ t)
    change B n 0 ω ≤ B n t ω at he
    simpa only [h0ω, Pi.zero_apply] using he
  have hBi (n : ℕ) (t : ℝ≥0) : Integrable (B n t) P :=
    hτ.integrable_continuous_compensator_neg_min hm hi hn hBM n t
  have hBmean (n : ℕ) (t : ℝ≥0) : (∫ ω, B n t ω ∂P) ≤ ∫ ω, C ω ∂P :=
    integral_clipped_compensator_le hτ hm hi hn hB0 hBM n t
  have hBindex (t : ℝ≥0) : HasMonotonePaths (fun n ω ↦ B n t ω) P := by
    apply ae_all_iff.mpr
    intro n
    apply ae_all_iff.mpr
    intro m
    by_cases hnm : n ≤ m
    · exact (hτ.ae_forall_le_continuous_compensators_neg_min
        hF hm hi hn hBcont hBv hB0 hBM hnm).mono fun _ hω _ ↦ hω t
    · exact Eventually.of_forall fun _ h ↦ (hnm h).elim
  have hBUI (t : ℝ≥0) : UniformIntegrable (fun n ↦ B n t) 1 P := by
    let G : Filtration ℕ mΩ := Filtration.const ℕ mΩ le_rfl
    have hGa : Adapted G (fun n ↦ B n t) :=
      fun n ↦ (hBa n t).mono (F.le t) le_rfl
    obtain ⟨_, _, _, hui, _⟩ :=
      (hBindex t).exists_integrable_limit_of_nonneg_of_integral_bounded hGa
        (fun n ↦ hBi n t) (fun n ↦ (hBnonneg n).mono fun _ hω ↦ hω t)
        (fun n ↦ hBmean n t)
    exact hui
  have hCauchy := hτ.cauchyUCP_continuous_compensators_neg_min
    hF hm hi hn hBcont hBv hB0 hBM
  have hR : TendstoInMeasure P (fun _ : ℕ ↦ (0 : Ω → ℝ)) atTop 0 :=
    (tendstoUCP_const (P := P) atTop (0 : ℝ≥0 → Ω → ℝ)).fixedTime 0
  have hgap : ∀ n, ∀ᵐ ω ∂P, ∀ t,
      ‖rightLimitProcess (B n) t ω - B n t ω‖ ≤ (0 : ℝ) := by
    intro n
    refine Eventually.of_forall fun ω t ↦ ?_
    rw [(IsContinuousPath.isRightContinuousPath (hBc n ω)).rightLimitProcess_eq,
      sub_self, norm_zero]
  obtain ⟨Y, hYa, hYc, hBY⟩ :=
    hCauchy.exists_everywhere_continuous_limit_of_caglad hBa hF
      (fun n ↦ (hBcont n).hasCagladPaths) hR hgap
  let A : ℝ≥0 → Ω → ℝ := fun t ω ↦ Y t ω - Y 0 ω
  have hAa : Adapted F A := fun t ↦
    (hYa t).sub ((hYa 0).mono (F.mono bot_le) le_rfl)
  have hAc (ω : Ω) : Continuous (A · ω) := (hYc ω).sub continuous_const
  have hA0 : A 0 = 0 := funext fun _ ↦ sub_self _
  have heYA : Indistinguishable Y A P := by
    filter_upwards [hBY.ae_eq_initial hB0] with ω hω t
    change Y t ω = Y t ω - Y 0 ω
    simp only [hω, Pi.zero_apply, sub_zero]
  have hBA : TendstoUCP P B atTop A := hBY.congr_right heYA
  have hAm : HasMonotonePaths A P := hBA.hasMonotonePaths hBm
  have hAn : ∀ᵐ ω ∂P, ∀ t : ℝ≥0, 0 ≤ A t ω :=
    hBA.ae_nonneg_of_monotone_zero hBm hB0
  have hAi (t : ℝ≥0) : Integrable (A t) P :=
    (hBUI t).integrable_of_tendstoInMeasure (hBA.fixedTime t)
  have hAmean (t : ℝ≥0) : (∫ ω, A t ω ∂P) ≤ ∫ ω, C ω ∂P := by
    have hL1 : Tendsto (fun n ↦ eLpNorm (B n t - A t) 1 P) atTop (𝓝 0) :=
      tendsto_Lp_finite_of_tendstoInMeasure le_rfl (by simp) (hBUI t).1
        (memLp_one_iff_integrable.mpr (hAi t)) (hBUI t).2.1 (hBA.fixedTime t)
    exact le_of_tendsto (tendsto_integral_of_L1' (A t) (hAi t).aestronglyMeasurable
      (Eventually.of_forall fun n ↦ hBi n t) hL1)
      (Eventually.of_forall fun n ↦ hBmean n t)
  have hJs (n : ℕ) : Supermartingale (J n) F P :=
    supermartingale_indicator_stoppingTime_le_neg_min hτ.1 hm hi hn (Nat.cast_nonneg n)
  have hXs : Supermartingale X F P :=
    supermartingale_indicator_stoppingTime_le hτ.1 hm.neg hi.neg
      (hn.mono fun _ hω ↦ neg_nonpos.mpr hω)
  have hJucp : TendstoUCP P J atTop X := by
    apply tendstoUCP_of_ae_compactDeviation
    · intro n T
      exact measurable_compactDeviation
        (fun t ↦ ((hJs n).stronglyAdapted t).measurable.mono (F.le t) le_rfl)
        (fun t ↦ (hXs.stronglyAdapted t).measurable.mono (F.le t) le_rfl)
        (fun ω ↦ (isCadlagPath_indicator_lifetime_le τ
          (fun ω ↦ -min (C ω) (n : ℝ)) ω).1)
        (fun ω ↦ (isCadlagPath_indicator_lifetime_le τ (fun ω ↦ -C ω) ω).1) T
    · refine Eventually.of_forall fun ω T ↦ ?_
      obtain ⟨N, hN⟩ := exists_nat_gt (C ω)
      apply tendsto_const_nhds.congr'
      filter_upwards [eventually_ge_atTop N] with n hn
      have hmin : min (C ω) (n : ℝ) = C ω :=
        min_eq_left (hN.le.trans (Nat.cast_le.mpr hn))
      simp only [compactDeviation, indicator_apply, hmin, sub_self, norm_zero,
        ENNReal.ofReal_zero, ENNReal.iSup_zero]
  have hJUI (t : ℝ≥0) : UniformIntegrable (fun n ↦ J n t) 1 P := by
    apply (uniformIntegrable_const le_rfl ENNReal.one_ne_top
      (memLp_one_iff_integrable.mpr hi)).mono_norm
      (fun n ↦ ((hJs n).integrable t).aestronglyMeasurable)
    intro n
    filter_upwards [hn] with ω hω
    apply (norm_indicator_le_norm_self _ _).trans
    rw [norm_neg, Real.norm_of_nonneg (le_min hω (Nat.cast_nonneg n)),
      Real.norm_of_nonneg hω]
    exact min_le_left _ _
  have hM : Martingale (X + A) F P :=
    martingale_of_tendstoInMeasure_uniformIntegrable hBM
      (fun t ↦ (hXs.stronglyAdapted t).add (hAa.stronglyAdapted t))
      (fun t ↦ (hJUI t).add (hBUI t) le_rfl)
      (fun t ↦ (hJucp.add hBA).fixedTime t)
  have hAcont : HasContinuousPaths A P := Eventually.of_forall hAc
  have hAcad : HasCadlagPaths A P := hAcont.hasCadlagPaths
  have hXc : HasCadlagPaths X P :=
    Eventually.of_forall (isCadlagPath_indicator_lifetime_le τ (fun ω ↦ -C ω))
  have hMc : HasCadlagPaths (X + A) P := hXc.add hAcad
  obtain ⟨Z, hiZ, hEZ, hboundZ, hlimZ, _, hL1Z⟩ :=
    hAm.exists_integrable_terminal_of_integral_bounded hAa hAi hAn hAmean
  have hAD : IsClassD A F P :=
    hAm.isClassD_of_nonneg_of_integral_bounded hAa hAi hAn hAmean hF
      hAcad.hasRightContinuousPaths
  have hXD : IsClassD X F P := isClassD_indicator_stoppingTime_le hτ.1 hm.neg hi.neg
  have hMD : IsClassD (X + A) F P := hXD.add hAD
  obtain ⟨L, hiL, hlimL, hL1L, hclose⟩ :=
    hM.exists_integrable_limit_of_uniformIntegrable hMc.hasRightContinuousPaths
      hMD.uniformIntegrable
  exact ⟨A, Z, L, hAa,
    hAa.isStronglyPredictable_of_leftContinuous (fun ω _ ↦ (hAc ω).continuousWithinAt),
    hAc, hA0, hAm, hAm.hasFiniteVariationPaths, hAD, hiZ, hEZ, hboundZ, hlimZ, hL1Z,
    hM, hMc, hMD, hMD.uniformIntegrable, hiL, hlimL, hL1L, hclose⟩

end ProbabilityTheory
