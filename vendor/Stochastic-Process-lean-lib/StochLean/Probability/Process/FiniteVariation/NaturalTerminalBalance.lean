/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Martingale.FiniteVariationIntegrand
public import StochLean.Probability.Martingale.Convergence.ContinuousL1Limit

/-! # Actual terminal integration-by-parts balance for integrable variation

All terminal variables below are constructed from the original processes.
The integral against the bounded martingale is a true UI martingale by an
actual integrable envelope, and its zero mean removes it from the terminal
expectation identity. No naturality or proposed terminal is assumed.
-/

@[expose] public section

open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsFiniteMeasure P]
  {F : Filtration ℝ≥0 mΩ} {A M : ℝ≥0 → Ω → ℝ}

/-- Actual terminal product expectation differs from the left-limit integral
expectation by exactly the actual raw bracket terminal expectation. The
initial product is retained in that raw bracket; A need not start at zero. -/
theorem HasIntegrableVariation.exists_integrable_terminals_integrationByParts
    (hv : HasIntegrableVariation A P) (ha : Adapted F A) (hc : HasCadlagPaths A P)
    (hi0 : Integrable (A 0) P) (hF : F.IsUsual P)
    (hM : Martingale M F P) (hcM : HasCadlagPaths M P)
    (C : ℝ) (hC : 0 ≤ C) (hb : ∀ᵐ ω ∂P, ∀ t, ‖M t ω‖ ≤ C) :
    let hSM := hM.isSemimartingale_of_bound hF hcM C hb
    let hSA := hv.hasFiniteVariationPaths.isSemimartingale ha hF hc
    let I := hSA.stochasticIntegral hF
      (hSM.adapted.leftLimitProcess_of_usual hF hcM) hcM.hasCagladPaths_leftLimitProcess
    let Q := hSM.quadraticCovariation hSA hF
    ∃ L B U V : Ω → ℝ, Integrable L P ∧ Integrable B P ∧ Integrable U P ∧ Integrable V P ∧
      (∀ᵐ ω ∂P, Tendsto (M · ω) atTop (𝓝 (L ω))) ∧
      (∀ᵐ ω ∂P, Tendsto (A · ω) atTop (𝓝 (B ω))) ∧
      (∀ᵐ ω ∂P, Tendsto (I · ω) atTop (𝓝 (U ω))) ∧
      (∀ᵐ ω ∂P, Tendsto (Q · ω) atTop (𝓝 (V ω))) ∧
      Integrable (fun ω ↦ L ω * B ω) P ∧
      (∫ ω, L ω * B ω ∂P) = (∫ ω, U ω ∂P) + ∫ ω, V ω ∂P := by
  intro hSM hSA I Q
  have huM : UniformIntegrable M 1 P := by
    apply (uniformIntegrable_const le_rfl ENNReal.one_ne_top
      (memLp_const C)).mono_norm (fun t ↦ (hM.integrable t).aestronglyMeasurable)
    intro t
    filter_upwards [hb] with ω hω
    exact (hω t).trans (le_abs_self C)
  obtain ⟨L, hiL, hlL, _, _⟩ :=
    hM.exists_integrable_limit_of_uniformIntegrable hcM.hasRightContinuousPaths huM
  have hbL : ∀ᵐ ω ∂P, ‖L ω‖ ≤ C := by
    filter_upwards [hlL, hb] with ω hω hbω
    exact le_of_tendsto hω.norm (Eventually.of_forall hbω)
  obtain ⟨B, hiB, hlB, _, _, _, _⟩ := hv.exists_integrable_terminal ha hF hc hi0
  have hbMl : ∀ᵐ ω ∂P, ∀ t, 0 < t → ‖leftLimitProcess M t ω‖ ≤ C := by
    filter_upwards [hcM, hb] with ω hω hbω t ht
    let : (𝓝[<] t).NeBot := nhdsLT_neBot_of_exists_lt ⟨0, ht⟩
    exact le_of_tendsto (hω.tendsto_leftLimitProcess ht.ne').norm
      (Eventually.of_forall hbω)
  have hiIl0 : Integrable (fun ω ↦ leftLimitProcess M 0 ω * A 0 ω) P := by
    simp only [leftLimitProcess_zero, Pi.zero_apply, zero_mul]
    exact ⟨aestronglyMeasurable_const, by simp [HasFiniteIntegral]⟩
  obtain ⟨U, hiU, hlU, _, _⟩ :=
    hSA.exists_integrable_terminal_stochasticIntegral_of_integrableVariation hF hv
      (hSM.adapted.leftLimitProcess_of_usual hF hcM) hcM.hasCagladPaths_leftLimitProcess
      hiIl0 hC hbMl
  obtain ⟨V, hiV, hlV, _, _⟩ :=
    hSM.exists_integrable_terminal_quadraticCovariation_of_right hSA hF hv hi0 hC hb
  let J := hSM.stochasticIntegral hF
    (ha.leftLimitProcess_of_usual hF hc) hc.hasCagladPaths_leftLimitProcess
  have huJ : IsUIMartingale J F P :=
    hM.isUIMartingale_stochasticIntegral_leftLimit_of_integrableVariation
      hF hcM ha hc hv hi0 hC hb
  have hcJ := hSM.hasCadlagPaths_stochasticIntegral hF
    (ha.leftLimitProcess_of_usual hF hc) hc.hasCagladPaths_leftLimitProcess
  obtain ⟨W, hiW, hlW, hLW, _⟩ := huJ.1.exists_integrable_limit_of_uniformIntegrable
    hcJ.hasRightContinuousPaths huJ.2
  have hmeanW : (∫ ω, W ω ∂P) = 0 := by
    have ht := tendsto_integral_of_L1' W hiW.aestronglyMeasurable
      (Eventually.of_forall huJ.1.integrable) hLW
    apply tendsto_nhds_unique ht
    have hz (t : ℝ≥0) : (∫ ω, J t ω ∂P) = 0 :=
      hM.integral_stochasticIntegral_leftLimit_eq_zero_of_integrableVariation
        hF hcM ha hc hv hi0 hC hb t
    simpa only [hz] using (tendsto_const_nhds :
      Tendsto (fun _ : ℝ≥0 ↦ (0 : ℝ)) atTop (𝓝 0))
  have hiProd : Integrable (fun ω ↦ L ω * B ω) P := by
    apply (hiB.norm.const_mul C).mono' (hiL.aestronglyMeasurable.mul hiB.aestronglyMeasurable)
    filter_upwards [hbL] with ω hω
    change ‖L ω * B ω‖ ≤ C * ‖B ω‖
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_right hω (norm_nonneg _)
  have hbalance : (fun ω ↦ L ω * B ω) =ᵐ[P] fun ω ↦ U ω + W ω + V ω := by
    filter_upwards [hlL, hlB, hlU, hlW, hlV, hSM.integrationByParts hSA hF]
      with ω hL hB hU hW hV he
    apply tendsto_nhds_unique (hL.mul hB)
    apply ((hU.add hW).add hV).congr'
    exact Eventually.of_forall fun t ↦ (he t).symm
  refine ⟨L, B, U, V, hiL, hiB, hiU, hiV, hlL, hlB, hlU, hlV, hiProd, ?_⟩
  have hs := integral_add (hiU.add hiW) hiV
  simp only [Pi.add_apply] at hs
  rw [integral_congr_ae hbalance, hs, integral_add hiU hiW, hmeanW, add_zero]

end ProbabilityTheory
