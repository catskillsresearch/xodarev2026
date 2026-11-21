/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Martingale.Doob.PredictableFiniteCorrections
public import StochLean.Probability.Martingale.Doob.PredictableSeriesRegularity
public import StochLean.Probability.Martingale.Doob.NonnegativeStepBudget
public import StochLean.Probability.Martingale.Convergence.InMeasureOrder
public import StochLean.Probability.Process.FiniteVariation.IntegrableTerminal
public import StochLean.Probability.Process.Stopping.PredictableJumpTests

/-! # Constructing the predictable jump correction of a Class D supermartingale

The original adapted cadlag process supplies a positive disjoint predictable
test cover. The coefficients are its actual negative conditional jump means.
Their nonnegativity and the supermartingale inequalities for the actual finite
corrections give a uniform first-moment budget. Class D supplies the required
lower expectation bound, so summability is a conclusion, not an input.

The original closed-step series is predictable, increasing, cadlag and of
integrable variation. Its finite corrected supermartingales converge in L1
at each fixed time, dominated by the actual summable coefficient envelope.
The resulting Class D supermartingale has zero mean jump at every positive
predictable test. This does not claim that its jumps are totally inaccessible.
No proposed correction, terminal value, series convergence or jump bound is
assumed, and all sampled jumps use explicit terminal zero at infinity.
-/

@[expose] public section

open ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology

namespace MeasureTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsFiniteMeasure P]
  {F : Filtration ℝ≥0 mΩ} {X : ℝ≥0 → Ω → ℝ}

/-- A genuine predictable increasing integrable-variation correction makes
any cadlag Class D supermartingale regular at every positive predictable test.
The entire correction, including its summable budget, is constructed from X. -/
theorem Supermartingale.exists_predictable_jump_mean_correction
    (hX : Supermartingale X F P) (hD : IsClassD X F P) (hF : F.IsUsual P)
    (hc : HasCadlagPaths X P) :
    ∃ A : ℝ≥0 → Ω → ℝ,
      IsStronglyPredictable F A ∧ HasCadlagPaths A P ∧ A 0 = 0 ∧
      HasMonotonePaths A P ∧ HasIntegrableVariation A P ∧ IsClassD A F P ∧
      Supermartingale (X + A) F P ∧ IsClassD (X + A) F P ∧
      HasCadlagPaths (X + A) P ∧
      ∀ (γ : Ω → WithTop ℝ≥0), IsPredictableStoppingTime F γ P →
        (∀ᵐ ω ∂P, 0 < γ ω) →
        Integrable
          (stoppedValueWithTerminal (jumpProcess (X + A)) (fun _ ↦ (0 : ℝ)) γ) P ∧
        (∫ ω, stoppedValueWithTerminal (jumpProcess (X + A))
          (fun _ ↦ (0 : ℝ)) γ ω ∂P) = 0 := by
  classical
  obtain ⟨Γ, hΓ, hpΓ, hdΓ, hcover⟩ :=
    hX.stronglyAdapted.adapted.exists_positive_disjoint_predictableStoppingTime_cover_jump_tests
      hF hc
  let K : ℕ → Ω → ℝ := fun n ↦
    -P[stoppedValueWithTerminal (jumpProcess X) (fun _ ↦ (0 : ℝ)) (Γ n) |
      (hΓ n).1.measurableSpaceBefore]
  let S : ℕ → ℝ≥0 → Ω → ℝ := fun N t ω ↦
    ∑ n ∈ Finset.range N, {v | Γ n v ≤ (t : WithTop ℝ≥0)}.indicator (K n) ω
  let A : ℝ≥0 → Ω → ℝ := fun t ω ↦
    ∑' n, {v | Γ n v ≤ (t : WithTop ℝ≥0)}.indicator (K n) ω
  have hdata := hX.predictable_jump_correction_coefficients hD hF hc Γ hΓ hpΓ
  have hmK (n : ℕ) : StronglyMeasurable[(hΓ n).1.measurableSpaceBefore] (K n) :=
    (hdata n).1
  have hiK (n : ℕ) : Integrable (K n) P := (hdata n).2.1
  have hnK (n : ℕ) : 0 ≤ᵐ[P] K n := (hdata n).2.2.1
  have hfinite := hX.finite_predictable_jump_corrections hD hF hc Γ hΓ hpΓ hdΓ
  have hM (N : ℕ) : Supermartingale (X + S N) F P := (hfinite.1 N).1
  obtain ⟨C, hC⟩ := hD.uniformIntegrable.2.2
  have hb (t : ℝ≥0) : -(∫ ω, X t ω ∂P) ≤ (C : ℝ) := by
    have he := hC t
    rw [eLpNorm_one_eq_lintegral_enorm,
      ← ofReal_integral_norm_eq_lintegral_enorm (hX.integrable t)] at he
    have hn : (∫ ω, ‖X t ω‖ ∂P) ≤ (C : ℝ) := by
      apply (ENNReal.ofReal_le_ofReal_iff C.coe_nonneg).mp
      simpa only [ENNReal.ofReal_coe_nnreal] using he
    exact (neg_le_abs _).trans ((norm_integral_le_integral_norm _).trans hn)
  have hs : Summable (fun n ↦ ∫ ω, ‖K n ω‖ ∂P) :=
    (hX.summable_integral_norm_of_nonnegative_step_corrections Γ K hiK hnK hpΓ
      (fun n ↦ (hdata n).2.2.2) hM C hb).1
  have hpA : IsStronglyPredictable F A :=
    isStronglyPredictable_tsum_indicator_stoppingTime_le hΓ hF.complete_initial hmK
  have hcA : HasCadlagPaths A P :=
    hasCadlagPaths_tsum_indicator_lifetime_le Γ hiK hs
  have hA0 : A 0 = 0 := by
    funext ω
    change (∑' n, {v | Γ n v ≤ ((0 : ℝ≥0) : WithTop ℝ≥0)}.indicator (K n) ω) = 0
    have he (n : ℕ) :
        {v | Γ n v ≤ ((0 : ℝ≥0) : WithTop ℝ≥0)}.indicator (K n) ω = 0 := by
      apply indicator_of_notMem
      exact not_le_of_gt (hpΓ n ω)
    simp only [he, tsum_zero]
  have hvA : HasIntegrableVariation A P :=
    hasIntegrableVariation_tsum_indicator_stoppingTime_le hF hΓ hmK hiK hs
  have hAD : IsClassD A F P :=
    hvA.isClassD hpA.stronglyAdapted.adapted hF hcA (by rw [hA0]; exact integrable_zero _ _ _)
  let G : Ω → ℝ := fun ω ↦ ∑' n, ‖K n ω‖
  obtain ⟨habs, hiG, _⟩ := ae_summable_norm_and_integrable_tsum_norm hiK hs
  have hmono : HasMonotonePaths A P := by
    filter_upwards [habs, ae_all_iff.mpr hnK] with ω hω hnω
    exact monotone_tsum_indicator_lifetime_le_of_nonneg Γ K hω hnω
  have hSM : Supermartingale (X + A) F P := by
    apply supermartingale_of_tendstoInMeasure_uniformIntegrable hM
      (hX.stronglyAdapted.add hpA.stronglyAdapted)
    · intro t
      have hG : Integrable (fun ω ↦ ‖X t ω‖ + G ω) P := (hX.integrable t).norm.add hiG
      apply (uniformIntegrable_const le_rfl ENNReal.one_ne_top
        (memLp_one_iff_integrable.mpr hG)).mono_norm
        (fun N ↦ ((hM N).integrable t).aestronglyMeasurable)
      intro N
      filter_upwards [habs] with ω hω
      change ‖X t ω + S N t ω‖ ≤ ‖‖X t ω‖ + G ω‖
      rw [Real.norm_of_nonneg
        (add_nonneg (norm_nonneg _) (tsum_nonneg fun n ↦ norm_nonneg (K n ω)))]
      apply (norm_add_le _ _).trans (add_le_add le_rfl ?_)
      exact (norm_sum_le _ _).trans
        ((Finset.sum_le_sum fun n _ ↦ norm_indicator_le_norm_self _ _).trans
          (hω.sum_le_tsum (Finset.range N) (fun n _ ↦ norm_nonneg (K n ω))))
    · intro t
      apply tendstoInMeasure_of_tendsto_ae
        (fun N ↦ ((hM N).integrable t).aestronglyMeasurable)
      filter_upwards [habs] with ω hω
      have hsum : Summable
          (fun n ↦ {v | Γ n v ≤ (t : WithTop ℝ≥0)}.indicator (K n) ω) :=
        hω.of_norm_bounded (fun n ↦ norm_indicator_le_norm_self _ _)
      exact tendsto_const_nhds.add hsum.hasSum.tendsto_sum_nat
  refine ⟨A, hpA, hcA, hA0, hmono, hvA, hAD, hSM, hD.add hAD, hc.add hcA, ?_⟩
  intro γ hγ hpos
  exact hX.stronglyAdapted.adapted.integrable_stopped_jump_and_integral_eq_zero_tsum_neg_condExp
    hD hF hc Γ hΓ hpΓ hdΓ hcover hs hγ hpos

end MeasureTheory
