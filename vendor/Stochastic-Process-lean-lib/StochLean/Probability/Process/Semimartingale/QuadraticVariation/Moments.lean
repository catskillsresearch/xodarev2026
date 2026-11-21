/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.Semimartingale.QuadraticVariation.Increasing
public import StochLean.Probability.Process.Semimartingale.StochasticIntegral.LocalL2
public import StochLean.Probability.Martingale.Inequalities.DoobContinuousL2

/-! # Finite-time second moments of the actual raw quadratic variation

The forward direction of Protter II.27, Corollary 3, for true square-integrable
cadlag martingales. The raw bracket retains the initial square. Doob domination
and Fatou first prove its integrability; dominated convergence then proves the
exact expectation identity. No bracket integrability is assumed.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsFiniteMeasure P]
  {F : Filtration ℝ≥0 mΩ} [SigmaFiniteFiltration P F] {X : ℝ≥0 → Ω → ℝ}

theorem IsSemimartingale.isLocalMartingale_sq_sub_quadraticVariation_of_locally_squareIntegrable
    (hX : IsSemimartingale X F P) (hF : F.IsUsual P)
    (hL : Locally (fun Y ↦ IsSquareIntegrableMartingale Y F P) F X P) :
    IsLocalMartingale (fun t ω ↦ (X t ω) ^ 2 - hX.quadraticVariation hF t ω) F P := by
  let ha := hX.adapted.leftLimitProcess_of_usual hF hX.hasCadlagPaths
  let hr := hX.hasCadlagPaths.hasCagladPaths_leftLimitProcess
  have hJ := hX.isLocalMartingale_stochasticIntegral_of_locally_squareIntegrable hF hL ha hr
  have he : (fun t ω ↦ (X t ω) ^ 2 - hX.quadraticVariation hF t ω) =
      (2 : ℝ) • hX.stochasticIntegral hF ha hr := by
    funext t ω
    simp only [IsSemimartingale.quadraticVariation, Pi.smul_apply, smul_eq_mul]
    ring
  rw [he]
  exact hJ.const_smul 2

/-- True finite-time L2 integrability implies integrability and the exact raw
bracket expectation at each finite time, including zero. -/
theorem IsSemimartingale.integrable_quadraticVariation_and_integral_eq
    (hX : IsSemimartingale X F P) (hF : F.IsUsual P)
    (hM : IsSquareIntegrableMartingale X F P) (T : ℝ≥0) :
    Integrable (hX.quadraticVariation hF T) P ∧
      (∫ ω, hX.quadraticVariation hF T ω ∂P) = ∫ ω, (X T ω) ^ 2 ∂P := by
  let Q := hX.quadraticVariation hF
  let N := fun t ω ↦ (X t ω) ^ 2 - Q t ω
  have hN : IsLocalMartingale N F P :=
    hX.isLocalMartingale_sq_sub_quadraticVariation_of_locally_squareIntegrable hF
      (Locally.of_prop hM)
  have hN0 : N 0 =ᵐ[P] fun _ ↦ 0 := by
    filter_upwards [hX.quadraticVariation_zero_ae hF] with ω hω
    simp only [N, Q, hω, sub_self]
  obtain ⟨τ, hτ⟩ := hN.2.2
  have hK := hτ.isKlenkeLocalizingSequence hN.1 ((integrable_const 0).congr hN0.symm)
  have hR (n : ℕ) : Martingale (MeasureTheory.stoppedProcess N (τ n)) F P := (hK.2.2 n).1
  obtain ⟨g, _, hg0, hg, hb, _⟩ := hM.1.exists_memLp_two_maximalEnvelope
    hX.hasCadlagPaths.hasRightContinuousPaths (hM.2 T)
  let U (n : ℕ) := MeasureTheory.stoppedProcess X (τ n) T
  let V (n : ℕ) := MeasureTheory.stoppedProcess Q (τ n) T
  have hUm (n : ℕ) : Measurable (U n) :=
    ((hM.1.stronglyAdapted.stoppedProcess_of_usual hF
      hX.hasCadlagPaths.hasRightContinuousPaths (hτ.1.isStoppingTime n) T).mono (F.le T)).measurable
  have hUb (n : ℕ) : ∀ᵐ ω ∂P, ‖U n ω‖ ≤ g ω := by
    filter_upwards [hb] with ω hω
    exact hω _ (WithTop.untopA_le (min_le_left (T : WithTop ℝ≥0) (τ n ω)))
  have hUsb (n : ℕ) : ∀ᵐ ω ∂P, ‖U n ω ^ 2‖ ≤ g ω ^ 2 := by
    filter_upwards [hUb n] with ω hω
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    simpa only [Real.norm_eq_abs, sq_abs] using
      (sq_le_sq₀ (norm_nonneg _) (hg0 ω)).mpr hω
  have hUi (n : ℕ) : Integrable (fun ω ↦ U n ω ^ 2) P :=
    hg.integrable_sq.mono' ((hUm n).pow_const 2).aestronglyMeasurable (hUsb n)
  have hsplit (n : ℕ) : V n = fun ω ↦ U n ω ^ 2 - MeasureTheory.stoppedProcess N (τ n) T ω := by
    funext ω
    change Q _ ω = X _ ω ^ 2 - (X _ ω ^ 2 - Q _ ω)
    ring
  have hVi (n : ℕ) : Integrable (V n) P := by
    rw [hsplit n]
    exact (hUi n).sub ((hR n).integrable T)
  have hRi (n : ℕ) : (∫ ω, MeasureTheory.stoppedProcess N (τ n) T ω ∂P) = 0 := by
    have he := (hR n).setIntegral_eq (show (0 : ℝ≥0) ≤ T from bot_le)
      (s := univ) MeasurableSet.univ
    simp only [Measure.restrict_univ] at he
    rw [← he]
    have hz : MeasureTheory.stoppedProcess N (τ n) 0 = N 0 :=
      funext fun _ ↦ stoppedProcess_eq_of_le bot_le
    rw [hz, integral_congr_ae hN0, integral_zero]
  have hEV (n : ℕ) : (∫ ω, V n ω ∂P) = ∫ ω, U n ω ^ 2 ∂P := by
    rw [hsplit n, integral_sub (hUi n) ((hR n).integrable T), hRi n, sub_zero]
  have hQnonneg : ∀ᵐ ω ∂P, ∀ t, 0 ≤ Q t ω :=
    (hX.initial_sq_le_quadraticVariation hF).mono fun ω hω t ↦ (sq_nonneg _).trans (hω t)
  have hVnonneg (n : ℕ) : ∀ᵐ ω ∂P, 0 ≤ V n ω :=
    hQnonneg.mono fun _ hω ↦ hω _
  have hevent (Z : ℝ≥0 → Ω → ℝ) :
      ∀ᵐ ω ∂P, ∀ᶠ n in atTop, MeasureTheory.stoppedProcess Z (τ n) T ω = Z T ω := by
    filter_upwards [hτ.1.tendsto_top] with ω hω
    filter_upwards [hω.eventually (Ioi_mem_nhds (WithTop.coe_lt_top T))] with n hn
    exact stoppedProcess_eq_of_le hn.le
  have hUsconv : ∀ᵐ ω ∂P, Tendsto (fun n ↦ U n ω ^ 2) atTop (𝓝 (X T ω ^ 2)) := by
    filter_upwards [hevent X] with ω hω
    exact tendsto_const_nhds.congr' (hω.mono fun n hn ↦ (congrArg (fun x : ℝ ↦ x ^ 2) hn).symm)
  have hVconv : ∀ᵐ ω ∂P, Tendsto (fun n ↦ V n ω) atTop (𝓝 (Q T ω)) := by
    filter_upwards [hevent Q] with ω hω
    exact tendsto_const_nhds.congr' (hω.mono fun _ hn ↦ hn.symm)
  have hEU : Tendsto (fun n ↦ ∫ ω, U n ω ^ 2 ∂P) atTop (𝓝 (∫ ω, X T ω ^ 2 ∂P)) :=
    tendsto_integral_of_dominated_convergence (fun ω ↦ g ω ^ 2)
      (fun n ↦ (hUi n).aestronglyMeasurable) hg.integrable_sq hUsb hUsconv
  have hELV : Tendsto (fun n ↦ ∫⁻ ω, ENNReal.ofReal (V n ω) ∂P) atTop
      (𝓝 (ENNReal.ofReal (∫ ω, X T ω ^ 2 ∂P))) := by
    have he (n : ℕ) : (∫⁻ ω, ENNReal.ofReal (V n ω) ∂P) =
        ENNReal.ofReal (∫ ω, U n ω ^ 2 ∂P) := by
      rw [← ofReal_integral_eq_lintegral_ofReal (hVi n) (hVnonneg n), hEV n]
    simpa only [he, Function.comp_def] using ENNReal.continuous_ofReal.continuousAt.tendsto.comp hEU
  have hFatou : (∫⁻ ω, ENNReal.ofReal (Q T ω) ∂P) ≤
      ENNReal.ofReal (∫ ω, X T ω ^ 2 ∂P) := by
    calc
      _ = ∫⁻ ω, liminf (fun n ↦ ENNReal.ofReal (V n ω)) atTop ∂P := by
        apply lintegral_congr_ae
        filter_upwards [hVconv] with ω hω
        exact (ENNReal.continuous_ofReal.continuousAt.tendsto.comp hω).liminf_eq.symm
      _ ≤ liminf (fun n ↦ ∫⁻ ω, ENNReal.ofReal (V n ω) ∂P) atTop :=
        lintegral_liminf_le' fun n ↦ (hVi n).aemeasurable.ennreal_ofReal
      _ = _ := hELV.liminf_eq
  have hQi : Integrable (Q T) P :=
    (lintegral_ofReal_ne_top_iff_integrable
      (((hX.adapted_quadraticVariation hF T).mono (F.le T) le_rfl).aestronglyMeasurable)
      (hQnonneg.mono fun _ hω ↦ hω T)).mp (hFatou.trans_lt ENNReal.ofReal_lt_top).ne
  have hVb (n : ℕ) : ∀ᵐ ω ∂P, ‖V n ω‖ ≤ Q T ω := by
    filter_upwards [hVnonneg n, hX.hasMonotonePaths_quadraticVariation hF] with ω hn hm
    rw [Real.norm_eq_abs, abs_of_nonneg hn]
    exact hm (WithTop.untopA_le (min_le_left (T : WithTop ℝ≥0) (τ n ω)))
  have hEVconv : Tendsto (fun n ↦ ∫ ω, V n ω ∂P) atTop (𝓝 (∫ ω, Q T ω ∂P)) :=
    tendsto_integral_of_dominated_convergence (Q T)
      (fun n ↦ (hVi n).aestronglyMeasurable) hQi hVb hVconv
  exact ⟨hQi, tendsto_nhds_unique hEVconv (hEU.congr' (Eventually.of_forall fun n ↦ (hEV n).symm))⟩

end ProbabilityTheory
