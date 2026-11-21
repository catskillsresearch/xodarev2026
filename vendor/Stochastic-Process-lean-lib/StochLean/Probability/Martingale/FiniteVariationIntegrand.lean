/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.FiniteVariation.Natural
public import StochLean.Probability.Process.Semimartingale.QuadraticCovariation.IntegrationByParts
public import StochLean.Probability.Process.Semimartingale.StochasticIntegral.IntegrableVariation
public import StochLean.Probability.Process.Semimartingale.StochasticIntegral.LocalL2
public import StochLean.Probability.Process.LocalMartingale.Bounded

/-! # Integrable-variation integrands against bounded martingales

The actual stochastic integral of the left limits of an adapted cadlag
integrable-variation process against a bounded cadlag martingale is a true
uniformly integrable martingale. The integrand need not be a martingale,
bounded, or square integrable. Its initial value is separately integrable.

Integration by parts constructs an integrable domination from the actual
variations of the finite-variation integral and raw mixed bracket. Their
initial values are retained; no candidate envelope or compensator is assumed.
-/

@[expose] public section

open ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology

namespace MeasureTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsFiniteMeasure P]
  {F : Filtration ℝ≥0 mΩ} {M A : ℝ≥0 → Ω → ℝ}

/-- The actual left-limit integral is uniformly integrable, without a bound
or martingale assumption on the integrable-variation integrand. -/
theorem Martingale.isUIMartingale_stochasticIntegral_leftLimit_of_integrableVariation
    (hM : Martingale M F P) (hF : F.IsUsual P) (hcM : HasCadlagPaths M P)
    (haA : Adapted F A) (hcA : HasCadlagPaths A P)
    (hvA : HasIntegrableVariation A P) (hiA0 : Integrable (A 0) P)
    {C : ℝ} (hC : 0 ≤ C) (hb : ∀ᵐ ω ∂P, ∀ t, ‖M t ω‖ ≤ C) :
    IsUIMartingale ((hM.isSemimartingale_of_bound hF hcM C hb).stochasticIntegral hF
      (haA.leftLimitProcess_of_usual hF hcA) hcA.hasCagladPaths_leftLimitProcess) F P := by
  let hSM := hM.isSemimartingale_of_bound hF hcM C hb
  let hSA := hvA.hasFiniteVariationPaths.isSemimartingale haA hF hcA
  let haLM := hSM.adapted.leftLimitProcess_of_usual hF hcM
  let hrLM := hcM.hasCagladPaths_leftLimitProcess
  let haLA := haA.leftLimitProcess_of_usual hF hcA
  let hrLA := hcA.hasCagladPaths_leftLimitProcess
  let I := hSA.stochasticIntegral hF haLM hrLM
  let J := hSM.stochasticIntegral hF haLA hrLA
  let Q := hSM.quadraticCovariation hSA hF
  have hbLM : ∀ᵐ ω ∂P, ∀ t, 0 < t → ‖leftLimitProcess M t ω‖ ≤ C := by
    filter_upwards [hcM, hb] with ω hcω hbω t ht
    let : (𝓝[<] t).NeBot := nhdsLT_neBot_of_exists_lt ⟨0, ht⟩
    exact le_of_tendsto (hcω.tendsto_leftLimitProcess ht.ne').norm
      (Eventually.of_forall hbω)
  have hvI : HasIntegrableVariation I P :=
    hSA.hasIntegrableVariation_stochasticIntegral hF hvA haLM hrLM hC hbLM
  have hI0 : I 0 =ᵐ[P] fun _ ↦ (0 : ℝ) := by
    simpa only [leftLimitProcess_zero, Pi.zero_apply, zero_mul] using
      hSA.stochasticIntegral_zero_ae hF haLM hrLM
  have hiI0 : Integrable (I 0) P := (integrable_const (0 : ℝ)).congr hI0.symm
  have hvQ : HasIntegrableVariation Q P :=
    hSM.hasIntegrableVariation_quadraticCovariation_of_right hSA hF hvA hC hb
  have hiMA0 : Integrable (fun ω ↦ M 0 ω * A 0 ω) P := by
    apply (hiA0.norm.const_mul C).mono'
      ((hM.integrable 0).aestronglyMeasurable.mul hiA0.aestronglyMeasurable)
    filter_upwards [hb] with ω hbω
    change ‖M 0 ω * A 0 ω‖ ≤ C * ‖A 0 ω‖
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_right (hbω 0) (norm_nonneg _)
  have hiQ0 : Integrable (Q 0) P :=
    hiMA0.congr (hSM.quadraticCovariation_zero_ae hSA hF).symm
  obtain ⟨_, _, _, _, _, heA, _⟩ :=
    hvA.exists_integrable_terminal haA hF hcA hiA0
  obtain ⟨_, _, _, _, _, heI, _⟩ := hvI.exists_integrable_terminal
    (hSA.adapted_stochasticIntegral hF haLM hrLM) hF
    (hSA.hasCadlagPaths_stochasticIntegral hF haLM hrLM) hiI0
  obtain ⟨_, _, _, _, _, heQ, _⟩ := hvQ.exists_integrable_terminal
    (hSM.adapted_quadraticCovariation hSA hF) hF
    (hSM.hasCadlagPaths_quadraticCovariation hSA hF) hiQ0
  let RA := fun ω ↦ ‖A 0 ω‖ + (eVariationOn (A · ω) univ).toReal
  let RI := fun ω ↦ ‖I 0 ω‖ + (eVariationOn (I · ω) univ).toReal
  let RQ := fun ω ↦ ‖Q 0 ω‖ + (eVariationOn (Q · ω) univ).toReal
  have hiRA : Integrable RA P := hiA0.norm.add hvA.integrable_eVariationOn_toReal
  have hiRI : Integrable RI P := hiI0.norm.add hvI.integrable_eVariationOn_toReal
  have hiRQ : Integrable RQ P := hiQ0.norm.add hvQ.integrable_eVariationOn_toReal
  have heIBP : Indistinguishable (M * A) (I + J + Q) P :=
    hSM.integrationByParts hSA hF
  have hJbound : ∀ᵐ ω ∂P, ∀ t, ‖J t ω‖ ≤ C * RA ω + RI ω + RQ ω := by
    filter_upwards [hb, heA, heI, heQ, heIBP] with ω hbω hAω hIω hQω heω t
    have he : M t ω * A t ω = I t ω + J t ω + Q t ω := heω t
    have hJ : J t ω = M t ω * A t ω - I t ω - Q t ω := by linarith
    calc
      ‖J t ω‖ = ‖M t ω * A t ω - I t ω - Q t ω‖ := congrArg norm hJ
      _ ≤ ‖M t ω * A t ω - I t ω‖ + ‖Q t ω‖ := norm_sub_le _ _
      _ ≤ (‖M t ω * A t ω‖ + ‖I t ω‖) + ‖Q t ω‖ :=
        add_le_add (norm_sub_le _ _) le_rfl
      _ = ‖M t ω‖ * ‖A t ω‖ + ‖I t ω‖ + ‖Q t ω‖ := by rw [norm_mul]
      _ ≤ C * RA ω + RI ω + RQ ω := add_le_add
        (add_le_add (mul_le_mul (hbω t) (hAω t) (norm_nonneg _) hC) (hIω t)) (hQω t)
  have hM2 : IsSquareIntegrableMartingale M F P := by
    refine ⟨hM, fun t ↦ ?_⟩
    exact MemLp.of_bound (hM.integrable t).aestronglyMeasurable C
      (hb.mono fun _ hω ↦ hω t)
  have hLJ : IsLocalMartingale J F P :=
    hSM.isLocalMartingale_stochasticIntegral_of_locally_squareIntegrable hF
      (Locally.of_prop hM2) haLA hrLA
  exact hLJ.isUIMartingale_of_integrable_envelope
    (((hiRA.const_mul C).add hiRI).add hiRQ) hJbound

/-- The left-limit convention gives initial value zero, so every actual
integral value has mean zero. -/
theorem Martingale.integral_stochasticIntegral_leftLimit_eq_zero_of_integrableVariation
    (hM : Martingale M F P) (hF : F.IsUsual P) (hcM : HasCadlagPaths M P)
    (haA : Adapted F A) (hcA : HasCadlagPaths A P)
    (hvA : HasIntegrableVariation A P) (hiA0 : Integrable (A 0) P)
    {C : ℝ} (hC : 0 ≤ C) (hb : ∀ᵐ ω ∂P, ∀ t, ‖M t ω‖ ≤ C) (t : ℝ≥0) :
    (∫ ω, (hM.isSemimartingale_of_bound hF hcM C hb).stochasticIntegral hF
      (haA.leftLimitProcess_of_usual hF hcA) hcA.hasCagladPaths_leftLimitProcess t ω ∂P) =
      0 := by
  let hSM := hM.isSemimartingale_of_bound hF hcM C hb
  let ha := haA.leftLimitProcess_of_usual hF hcA
  let hr := hcA.hasCagladPaths_leftLimitProcess
  let J := hSM.stochasticIntegral hF ha hr
  have hJ : Martingale J F P :=
    (hM.isUIMartingale_stochasticIntegral_leftLimit_of_integrableVariation
      hF hcM haA hcA hvA hiA0 hC hb).1
  have hz : J 0 =ᵐ[P] fun _ ↦ (0 : ℝ) := by
    simpa only [leftLimitProcess_zero, Pi.zero_apply, zero_mul] using
      hSM.stochasticIntegral_zero_ae hF ha hr
  have he := hJ.setIntegral_eq (bot_le : (0 : ℝ≥0) ≤ t)
    (@MeasurableSet.univ Ω (F 0))
  rw [setIntegral_univ, setIntegral_univ] at he
  change (∫ ω, J 0 ω ∂P) = ∫ ω, J t ω ∂P at he
  rw [integral_congr_ae hz, integral_zero] at he
  exact he.symm

end MeasureTheory
