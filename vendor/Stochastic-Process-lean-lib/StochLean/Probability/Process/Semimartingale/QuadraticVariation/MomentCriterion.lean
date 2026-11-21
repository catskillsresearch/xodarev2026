/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.Semimartingale.QuadraticVariation.Moments
public import StochLean.Probability.Process.Semimartingale.QuadraticVariation.JumpLocalization
public import StochLean.Probability.Process.Semimartingale.LocalL2Martingale

/-! # The raw bracket moment criterion on the semimartingale domain

Bracket integrability constructs L2 localizers, whose square-minus-bracket
residuals become true martingales by domination. Their uniform second moments
and Doob estimates pass to the original process by Fatou. Only then is the
original local martingale proved to be a true square-integrable martingale.
The semimartingale witness is explicit until the general LM-to-SM bridge exists.
-/

@[expose] public section

open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsFiniteMeasure P]
  {F : Filtration ℝ≥0 mΩ} [SigmaFiniteFiltration P F] {X : ℝ≥0 → Ω → ℝ}

theorem IsSemimartingale.lintegral_denseRunningSupremum_sq_le_of_integrable_quadraticVariation
    (hX : IsSemimartingale X F P) (hF : F.IsUsual P) (hM : IsLocalMartingale X F P)
    (hQ : ∀ T, Integrable (hX.quadraticVariation hF T) P) (T : ℝ≥0) :
    (∫⁻ ω, denseRunningSupremum (fun t ω ↦ X t ω ^ 2) T ω ∂P) ≤
      4 * ENNReal.ofReal (∫ ω, hX.quadraticVariation hF T ω ∂P) := by
  let Q := hX.quadraticVariation hF
  let N := fun t ω ↦ X t ω ^ 2 - Q t ω
  have hL := hX.locally_squareIntegrableMartingale_of_integrable_quadraticVariation hF hM hQ
  have hN : IsLocalMartingale N F P :=
    hX.isLocalMartingale_sq_sub_quadraticVariation_of_locally_squareIntegrable hF hL
  have hN0 : N 0 =ᵐ[P] fun _ ↦ 0 := by
    filter_upwards [hX.quadraticVariation_zero_ae hF] with ω hω
    simp only [N, Q, hω, sub_self]
  obtain ⟨τ, hτ, hYsq⟩ := hL
  let Y (n : ℕ) := MeasureTheory.stoppedProcess
    (fun t ↦ {ω | 0 < τ n ω}.indicator (X t)) (τ n)
  have hYs (n : ℕ) : IsSquareIntegrableMartingale (Y n) F P := by
    simpa only [Y, bot_eq_zero] using hYsq n
  let R (n : ℕ) := MeasureTheory.stoppedProcess
    (fun t ↦ {ω | 0 < τ n ω}.indicator (N t)) (τ n)
  let V (n : ℕ) := MeasureTheory.stoppedProcess
    (fun t ↦ {ω | 0 < τ n ω}.indicator (Q t)) (τ n)
  have hR (n : ℕ) : IsLocalMartingale (R n) F P :=
    hN.masked_stoppedProcess hF (hτ.isStoppingTime n)
  have hsplit (n : ℕ) (t : ℝ≥0) (ω : Ω) : R n t ω = Y n t ω ^ 2 - V n t ω := by
    simp only [R, Y, V, stoppedProcess_indicator_comm]
    by_cases hp : ω ∈ {v | 0 < τ n v}
    · simp only [indicator_of_mem hp]
      rfl
    · simp only [indicator_of_notMem hp, zero_pow (by decide : 2 ≠ 0), sub_zero]
  have hQn : ∀ᵐ ω ∂P, ∀ t, 0 ≤ Q t ω :=
    (hX.initial_sq_le_quadraticVariation hF).mono fun _ hω t ↦ (sq_nonneg _).trans (hω t)
  have hVb (n : ℕ) (S : ℝ≥0) : ∀ᵐ ω ∂P, ∀ t ≤ S, 0 ≤ V n t ω ∧ V n t ω ≤ Q S ω := by
    filter_upwards [hQn, hX.hasMonotonePaths_quadraticVariation hF] with ω hn hm t ht
    dsimp only [V]
    rw [stoppedProcess_indicator_comm]
    by_cases hp : ω ∈ {v | 0 < τ n v}
    · rw [indicator_of_mem hp]
      exact ⟨hn _, hm ((WithTop.untopA_le (min_le_left _ _)).trans ht)⟩
    · rw [indicator_of_notMem hp]
      exact ⟨le_rfl, hn S⟩
  have hRm (n : ℕ) : Martingale (R n) F P := by
    apply (hR n).martingale_of_integrable_envelope
    intro S
    obtain ⟨g, _, hg0, hg, hb, _⟩ := (hYs n).1.exists_memLp_two_maximalEnvelope
      ((hX.hasCadlagPaths.indicator _).stoppedProcess (τ n)).hasRightContinuousPaths
        ((hYs n).2 S)
    refine ⟨fun ω ↦ g ω ^ 2 + Q S ω, hg.integrable_sq.add (hQ S), ?_⟩
    filter_upwards [hb, hVb n S] with ω hω hv t ht
    have hys : ‖Y n t ω ^ 2‖ ≤ g ω ^ 2 := by
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      simpa only [Y, bot_eq_zero, Real.norm_eq_abs, sq_abs] using
        (sq_le_sq₀ (norm_nonneg _) (hg0 ω)).mpr (hω t ht)
    have hvs : ‖V n t ω‖ ≤ Q S ω := by
      rw [Real.norm_eq_abs, abs_of_nonneg (hv t ht).1]
      exact (hv t ht).2
    rw [hsplit]
    exact (norm_sub_le _ _).trans (add_le_add hys hvs)
  have hVi (n : ℕ) (S : ℝ≥0) : Integrable (V n S) P := by
    apply (((hYs n).2 S).integrable_sq.sub ((hRm n).integrable S)).congr
    apply Eventually.of_forall
    intro ω
    change Y n S ω ^ 2 - R n S ω = V n S ω
    rw [hsplit]
    ring
  have hRi (n : ℕ) (S : ℝ≥0) : (∫ ω, R n S ω ∂P) = 0 := by
    have he := (hRm n).setIntegral_eq (show (0 : ℝ≥0) ≤ S from bot_le)
      (s := univ) MeasurableSet.univ
    simp only [Measure.restrict_univ] at he
    rw [← he]
    have hz : R n 0 =ᵐ[P] fun _ ↦ 0 := by
      filter_upwards [hN0] with ω hω
      change MeasureTheory.stoppedProcess
        (fun t ↦ {ω | 0 < τ n ω}.indicator (N t)) (τ n) 0 ω = 0
      rw [stoppedProcess_eq_of_le (show (0 : WithTop ℝ≥0) ≤ τ n ω from bot_le)]
      by_cases hp : ω ∈ {v | 0 < τ n v}
      · simpa only [indicator_of_mem hp] using hω
      · exact indicator_of_notMem hp _
    rw [integral_congr_ae hz, integral_zero]
  have hEY (n : ℕ) (S : ℝ≥0) : (∫ ω, Y n S ω ^ 2 ∂P) ≤ ∫ ω, Q S ω ∂P := by
    have he := integral_congr_ae (μ := P) (Eventually.of_forall (hsplit n S))
    rw [hRi n S, integral_sub ((hYs n).2 S).integrable_sq (hVi n S)] at he
    have hb := integral_mono_ae (hVi n S) (hQ S)
      ((hVb n S).mono fun _ hω ↦ (hω S le_rfl).2)
    linarith
  let G (n : ℕ) := denseRunningSupremum (fun t ω ↦ Y n t ω ^ 2) T
  have hGm (n : ℕ) : Measurable (G n) :=
    measurable_denseRunningSupremum (fun t ↦
      (((hYs n).1.stronglyAdapted t).mono (F.le t)).measurable.pow_const 2) T
  have hGb (n : ℕ) : (∫⁻ ω, G n ω ∂P) ≤ 4 * ENNReal.ofReal (∫ ω, Q T ω ∂P) := by
    have hd := (hYs n).1.lintegral_denseRunningSupremum_norm_sq_le ((hYs n).2 T)
    simp only [Real.norm_eq_abs, sq_abs] at hd
    exact hd.trans (mul_le_mul le_rfl (ENNReal.ofReal_le_ofReal (hEY n T))
      (by positivity) (by positivity))
  have hGevent : ∀ᵐ ω ∂P, ∀ᶠ n in atTop,
      G n ω = denseRunningSupremum (fun t ω ↦ X t ω ^ 2) T ω := by
    filter_upwards [hτ.tendsto_top] with ω hω
    filter_upwards [hω.eventually (Ioi_mem_nhds (WithTop.coe_lt_top T))] with n hn
    have he (t : ℝ≥0) (ht : t ≤ T) : Y n t ω = X t ω := by
      change MeasureTheory.stoppedProcess
        (fun t ↦ {ω | 0 < τ n ω}.indicator (X t)) (τ n) t ω = X t ω
      rw [stoppedProcess_eq_of_le ((WithTop.coe_le_coe.mpr ht).trans hn.le)]
      exact indicator_of_mem (show ω ∈ {v | 0 < τ n v} from lt_of_le_of_lt bot_le hn) _
    change (⨆ k, ENNReal.ofReal (Y n (denseTimeUpTo T k) ω ^ 2)) =
      ⨆ k, ENNReal.ofReal (X (denseTimeUpTo T k) ω ^ 2)
    apply iSup_congr
    intro k
    rw [he (denseTimeUpTo T k) (min_le_left _ _)]
  calc
    _ = ∫⁻ ω, liminf (fun n ↦ G n ω) atTop ∂P := by
      apply lintegral_congr_ae
      filter_upwards [hGevent] with ω hω
      have hlim : Tendsto (fun n ↦ G n ω) atTop
          (𝓝 (denseRunningSupremum (fun t ω ↦ X t ω ^ 2) T ω)) :=
        tendsto_const_nhds.congr' (hω.mono fun _ h ↦ h.symm)
      exact hlim.liminf_eq.symm
    _ ≤ liminf (fun n ↦ ∫⁻ ω, G n ω ∂P) atTop := lintegral_liminf_le' fun n ↦ (hGm n).aemeasurable
    _ ≤ _ := liminf_le_of_frequently_le (Eventually.of_forall hGb).frequently

/-- Bracket integrability proves the original process is a true martingale,
not merely that its deterministic-time values belong to L2. -/
theorem IsSemimartingale.isSquareIntegrableMartingale_of_integrable_quadraticVariation
    (hX : IsSemimartingale X F P) (hF : F.IsUsual P) (hM : IsLocalMartingale X F P)
    (hQ : ∀ T, Integrable (hX.quadraticVariation hF T) P) :
    IsSquareIntegrableMartingale X F P := by
  let A (T : ℝ≥0) := denseRunningSupremum (fun t ω ↦ X t ω ^ 2) T
  have hAm (T : ℝ≥0) : Measurable (A T) :=
    measurable_denseRunningSupremum (fun t ↦
      ((hX.adapted t).mono (F.le t) le_rfl).pow_const 2) T
  have hAfin (T : ℝ≥0) : (∫⁻ ω, A T ω ∂P) ≠ ∞ :=
    ((hX.lintegral_denseRunningSupremum_sq_le_of_integrable_quadraticVariation hF hM hQ T).trans_lt
      (ENNReal.mul_lt_top (by norm_num) ENNReal.ofReal_lt_top)).ne
  let g (T : ℝ≥0) (ω : Ω) := Real.sqrt (A T ω).toReal
  have hglp (T : ℝ≥0) : MemLp (g T) 2 P := by
    apply (memLp_two_iff_integrable_sq
      (hAm T).ennreal_toReal.sqrt.aestronglyMeasurable).mpr
    simpa only [Real.sq_sqrt ENNReal.toReal_nonneg] using
      integrable_toReal_of_lintegral_ne_top (hAm T).aemeasurable (hAfin T)
  have hb (T : ℝ≥0) : ∀ᵐ ω ∂P, ∀ t ≤ T, ‖X t ω‖ ≤ g T ω := by
    filter_upwards [ae_lt_top (hAm T) (hAfin T),
      hX.hasCadlagPaths.hasRightContinuousPaths] with ω hfin hcont t ht
    apply Real.le_sqrt_of_sq_le
    rw [Real.norm_eq_abs, sq_abs]
    exact (ENNReal.ofReal_le_iff_le_toReal hfin.ne).mp
      (ofReal_le_denseRunningSupremum_of_rightContinuous ht (fun s ↦ (hcont s).pow 2))
  refine ⟨hM.martingale_of_integrable_envelope (fun T ↦
    ⟨g T, (hglp T).integrable (by norm_num), hb T⟩), fun T ↦ ?_⟩
  exact (hglp T).mono' (((hX.adapted T).mono (F.le T) le_rfl).aestronglyMeasurable)
    ((hb T).mono fun _ hω ↦ hω T le_rfl)

/-- The finite-time moment equivalence with its actual raw bracket owner.
No infinite-terminal or general LM-to-SM assertion is implicit in this theorem. -/
theorem IsSemimartingale.squareIntegrableMartingale_iff_integrable_quadraticVariation
    (hX : IsSemimartingale X F P) (hF : F.IsUsual P) (hM : IsLocalMartingale X F P) :
    IsSquareIntegrableMartingale X F P ↔ ∀ T, Integrable (hX.quadraticVariation hF T) P :=
  ⟨fun hm T ↦ (hX.integrable_quadraticVariation_and_integral_eq hF hm T).1,
    fun hQ ↦ hX.isSquareIntegrableMartingale_of_integrable_quadraticVariation hF hM hQ⟩

/-- For continuous local martingales the semimartingale witness is already
constructed internally, so no additional good-integrator premise is required. -/
theorem IsContinuousLocalMartingale.squareIntegrableMartingale_iff_integrable_quadraticVariation
    (hX : IsContinuousLocalMartingale X F P) (hF : F.IsUsual P) :
    IsSquareIntegrableMartingale X F P ↔
      ∀ T, Integrable ((hX.isSemimartingale hF).quadraticVariation hF T) P :=
  (hX.isSemimartingale hF).squareIntegrableMartingale_iff_integrable_quadraticVariation hF hX.1

/-- For a true L2 cadlag martingale the compensated square is a true
martingale, not just a local martingale. The raw convention makes its initial
value zero even when the original initial value is nonzero. -/
theorem IsSemimartingale.martingale_sq_sub_quadraticVariation_of_squareIntegrable
    (hX : IsSemimartingale X F P) (hF : F.IsUsual P)
    (hM : IsSquareIntegrableMartingale X F P) :
    Martingale (fun t ω ↦ X t ω ^ 2 - hX.quadraticVariation hF t ω) F P := by
  apply (hX.isLocalMartingale_sq_sub_quadraticVariation_of_locally_squareIntegrable
    hF (Locally.of_prop hM)).martingale_of_integrable_envelope
  intro T
  obtain ⟨g, _, hg0, hg, hb, _⟩ := hM.1.exists_memLp_two_maximalEnvelope
    hX.hasCadlagPaths.hasRightContinuousPaths (hM.2 T)
  have hQi := (hX.integrable_quadraticVariation_and_integral_eq hF hM T).1
  refine ⟨fun ω ↦ g ω ^ 2 + hX.quadraticVariation hF T ω, hg.integrable_sq.add hQi, ?_⟩
  filter_upwards [hb, hX.initial_sq_le_quadraticVariation hF,
    hX.hasMonotonePaths_quadraticVariation hF] with ω hω h0 hmono t ht
  have hys : ‖X t ω ^ 2‖ ≤ g ω ^ 2 := by
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    simpa only [Real.norm_eq_abs, sq_abs] using
      (sq_le_sq₀ (norm_nonneg _) (hg0 ω)).mpr (hω t ht)
  have hqs : ‖hX.quadraticVariation hF t ω‖ ≤ hX.quadraticVariation hF T ω := by
    rw [Real.norm_eq_abs, abs_of_nonneg ((sq_nonneg _).trans (h0 t))]
    exact hmono ht
  exact (norm_sub_le _ _).trans (add_le_add hys hqs)

end ProbabilityTheory
