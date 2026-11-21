/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.FiniteVariation.Jordan
public import StochLean.Probability.Martingale.Convergence.ContinuousMonotoneL1

/-! # Integrable terminal limits under total-variation domination

The existing positive and negative variation processes start at zero and
are increasing on finite-variation paths. Their sum is the existing total
variation process. An integrable common bound therefore lets the established
monotone-process terminal theorem construct both actual Jordan terminals.
Reconstruction retains the original initial random variable.

The assumed integrability of the initial value is independent of variation
integrability: a random constant has zero variation without necessarily
being integrable. The domination variable is a generic input, not a newly
defined global variation or a substitute terminal selector.
-/

@[expose] public section

open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
  {X : ℝ≥0 → Ω → ℝ} {V : Ω → ℝ}

private theorem ae_jordan_bounds (hv : HasFiniteVariationPaths X P)
    (hV : ∀ᵐ ω ∂P, ∀ t, totalVariationProcess X t ω ≤ V ω) :
    ∀ᵐ ω ∂P, ∀ t,
      (0 ≤ positiveVariationProcess X t ω ∧ positiveVariationProcess X t ω ≤ V ω) ∧
      (0 ≤ negativeVariationProcess X t ω ∧ negativeVariationProcess X t ω ≤ V ω) := by
  filter_upwards [hv.hasMonotonePaths_positiveVariationProcess,
    hv.hasMonotonePaths_negativeVariationProcess, hV] with ω hp hn hω t
  have hp0 := hp (bot_le : (0 : ℝ≥0) ≤ t)
  have hn0 := hn (bot_le : (0 : ℝ≥0) ≤ t)
  change positiveVariationProcess X 0 ω ≤ positiveVariationProcess X t ω at hp0
  change negativeVariationProcess X 0 ω ≤ negativeVariationProcess X t ω at hn0
  simp only [positiveVariationProcess_zero, Pi.zero_apply] at hp0
  simp only [negativeVariationProcess_zero, Pi.zero_apply] at hn0
  have hs := congrFun (congrFun (positiveVariationProcess_add_negative X) t) ω
  change positiveVariationProcess X t ω + negativeVariationProcess X t ω =
    totalVariationProcess X t ω at hs
  exact ⟨⟨hp0, by linarith [hω t]⟩, ⟨hn0, by linarith [hω t]⟩⟩

/-- Variation controls increments, so a whole-path norm bound must retain
the initial value. No measurability or integrability is needed for this bound. -/
theorem HasFiniteVariationPaths.ae_norm_le_initial_add_of_totalVariation_le
    (hv : HasFiniteVariationPaths X P)
    (hV : ∀ᵐ ω ∂P, ∀ t, totalVariationProcess X t ω ≤ V ω) :
    ∀ᵐ ω ∂P, ∀ t, ‖X t ω‖ ≤ ‖X 0 ω‖ + V ω := by
  filter_upwards [ae_jordan_bounds hv hV, hV] with ω hj hω t
  have hs := congrFun (congrFun (positiveVariationProcess_add_negative X) t) ω
  change positiveVariationProcess X t ω + negativeVariationProcess X t ω =
    totalVariationProcess X t ω at hs
  rw [finiteVariationProcess_reconstruction X t ω]
  calc
    _ ≤ ‖X 0 ω + positiveVariationProcess X t ω‖ +
        ‖negativeVariationProcess X t ω‖ := norm_sub_le _ _
    _ ≤ (‖X 0 ω‖ + ‖positiveVariationProcess X t ω‖) +
        ‖negativeVariationProcess X t ω‖ := add_le_add (norm_add_le _ _) le_rfl
    _ = ‖X 0 ω‖ + totalVariationProcess X t ω := by
      rw [Real.norm_of_nonneg (hj t).1.1, Real.norm_of_nonneg (hj t).2.1]
      linarith
    _ ≤ ‖X 0 ω‖ + V ω := add_le_add le_rfl (hω t)

variable [IsFiniteMeasure P] {F : Filtration ℝ≥0 mΩ}

/-- An adapted cadlag finite-variation process with integrable initial value
and integrably dominated whole-time variation has an actual integrable
terminal limit, all-time L1 convergence, and Class D. -/
theorem HasFiniteVariationPaths.exists_integrable_terminal_of_totalVariation_le
    (hv : HasFiniteVariationPaths X P) (ha : Adapted F X) (hF : F.IsUsual P)
    (hc : HasCadlagPaths X P) (hi0 : Integrable (X 0) P) (hiV : Integrable V P)
    (hV : ∀ᵐ ω ∂P, ∀ t, totalVariationProcess X t ω ≤ V ω) :
    ∃ Z : Ω → ℝ, Integrable Z P ∧
      (∀ᵐ ω ∂P, Tendsto (fun t : ℝ≥0 ↦ X t ω) atTop (𝓝 (Z ω))) ∧
      Tendsto (fun t : ℝ≥0 ↦ eLpNorm (X t - Z) 1 P) atTop (𝓝 0) ∧
      IsClassD X F P ∧
      (∀ᵐ ω ∂P, ∀ t, ‖X t ω‖ ≤ ‖X 0 ω‖ + V ω) ∧
      ∀ᵐ ω ∂P, ‖Z ω‖ ≤ ‖X 0 ω‖ + V ω := by
  have hj := ae_jordan_bounds hv hV
  have hpa := ha.positiveVariationProcess_of_usual hF hc
  have hna := ha.negativeVariationProcess_of_usual hF hc
  have hpi (t : ℝ≥0) : Integrable (positiveVariationProcess X t) P := by
    apply hiV.mono' ((hpa t).mono (F.le t) le_rfl).aestronglyMeasurable
    filter_upwards [hj] with ω hω
    rw [Real.norm_of_nonneg (hω t).1.1]
    exact (hω t).1.2
  have hni (t : ℝ≥0) : Integrable (negativeVariationProcess X t) P := by
    apply hiV.mono' ((hna t).mono (F.le t) le_rfl).aestronglyMeasurable
    filter_upwards [hj] with ω hω
    rw [Real.norm_of_nonneg (hω t).2.1]
    exact (hω t).2.2
  obtain ⟨Zp, hip, _, _, hlp, _, _⟩ :=
    hv.hasMonotonePaths_positiveVariationProcess.exists_integrable_terminal_of_integral_bounded
      hpa hpi (hj.mono fun _ hω t ↦ (hω t).1.1)
      (fun t ↦ integral_mono_ae (hpi t) hiV (hj.mono fun _ hω ↦ (hω t).1.2))
  obtain ⟨Zn, hin, _, _, hln, _, _⟩ :=
    hv.hasMonotonePaths_negativeVariationProcess.exists_integrable_terminal_of_integral_bounded
      hna hni (hj.mono fun _ hω t ↦ (hω t).2.1)
      (fun t ↦ integral_mono_ae (hni t) hiV (hj.mono fun _ hω ↦ (hω t).2.2))
  let Z : Ω → ℝ := X 0 + Zp - Zn
  have hiZ : Integrable Z P := (hi0.add hip).sub hin
  have hl : ∀ᵐ ω ∂P, Tendsto (fun t : ℝ≥0 ↦ X t ω) atTop (𝓝 (Z ω)) := by
    filter_upwards [hlp, hln] with ω hp hn
    have h := ((tendsto_const_nhds :
      Tendsto (fun _ : ℝ≥0 ↦ X 0 ω) atTop (𝓝 (X 0 ω))).add hp).sub hn
    exact h.congr' (Eventually.of_forall fun t ↦ (finiteVariationProcess_reconstruction X t ω).symm)
  let W : Ω → ℝ := fun ω ↦ ‖X 0 ω‖ + V ω
  have hiW : Integrable W P := hi0.norm.add hiV
  have hbX : ∀ᵐ ω ∂P, ∀ t, ‖X t ω‖ ≤ W ω :=
    hv.ae_norm_le_initial_add_of_totalVariation_le hV
  have hbZ : ∀ᵐ ω ∂P, ‖Z ω‖ ≤ W ω := by
    filter_upwards [hl, hbX] with ω hlω hω
    exact le_of_tendsto hlω.norm (Eventually.of_forall hω)
  have hiX (t : ℝ≥0) : Integrable (X t) P :=
    hiW.mono' ((ha t).mono (F.le t) le_rfl).aestronglyMeasurable
      (hbX.mono fun _ hω ↦ hω t)
  have hnorm : Tendsto (fun t : ℝ≥0 ↦ ∫ ω, ‖X t ω - Z ω‖ ∂P) atTop (𝓝 0) := by
    have hmeas : ∀ᶠ t : ℝ≥0 in atTop,
        AEStronglyMeasurable (fun ω ↦ ‖X t ω - Z ω‖) P :=
      Eventually.of_forall fun t ↦ ((hiX t).sub hiZ).aestronglyMeasurable.norm
    have hb : ∀ᶠ t : ℝ≥0 in atTop, ∀ᵐ ω ∂P, ‖‖X t ω - Z ω‖‖ ≤ 2 * W ω := by
      refine Eventually.of_forall fun t ↦ ?_
      filter_upwards [hbX, hbZ] with ω hω hz
      rw [norm_norm]
      exact (norm_sub_le _ _).trans ((add_le_add (hω t) hz).trans_eq (two_mul _).symm)
    have hnlim : ∀ᵐ ω ∂P,
        Tendsto (fun t : ℝ≥0 ↦ ‖X t ω - Z ω‖) atTop (𝓝 (0 : ℝ)) := by
      filter_upwards [hl] with ω hω
      have hconst : Tendsto (fun _ : ℝ≥0 ↦ Z ω) atTop (𝓝 (Z ω)) := tendsto_const_nhds
      simpa only [sub_self, norm_zero] using (hω.sub hconst).norm
    simpa only [integral_zero] using
      tendsto_integral_filter_of_dominated_convergence (fun ω ↦ 2 * W ω)
        hmeas hb (hiW.const_mul 2) hnlim
  have hL1 : Tendsto (fun t : ℝ≥0 ↦ eLpNorm (X t - Z) 1 P) atTop (𝓝 0) := by
    have he (t : ℝ≥0) : eLpNorm (X t - Z) 1 P =
        ENNReal.ofReal (∫ ω, ‖X t ω - Z ω‖ ∂P) := by
      rw [eLpNorm_one_eq_lintegral_enorm]
      exact (ofReal_integral_norm_eq_lintegral_enorm ((hiX t).sub hiZ)).symm
    simp_rw [he]
    simpa only [Function.comp_def, ENNReal.ofReal_zero] using
      (ENNReal.continuous_ofReal.tendsto (0 : ℝ)).comp hnorm
  have hD : IsClassD X F P := by
    apply (isClassD_const (F := F) hiW).mono_norm
    · intro σ
      have hm := ha.stronglyAdapted.measurable_stoppedValue_of_usual hF
        hc.hasRightContinuousPaths σ.isStoppingTime
      exact (hm.mono σ.measurableSpace_le le_rfl).aestronglyMeasurable
    · intro σ
      filter_upwards [hbX] with ω hω
      have hb := hω (σ ω)
      rw [Real.norm_of_nonneg ((norm_nonneg _).trans hb)]
      exact hb
  exact ⟨Z, hiZ, hl, hL1, hD, hbX, hbZ⟩

end ProbabilityTheory
