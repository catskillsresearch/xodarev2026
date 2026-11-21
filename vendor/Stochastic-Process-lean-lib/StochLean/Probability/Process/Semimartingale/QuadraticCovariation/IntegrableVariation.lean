/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.Semimartingale.QuadraticCovariation.PureJump
public import StochLean.Probability.Process.FiniteVariation.IntegrableTerminal
public import StochLean.Analysis.PathVariation.StieltjesCountableSupport
public import StochLean.Analysis.PathVariation.StieltjesIntegralVariation

/-! # Integrable variation of the actual mixed bracket

A bounded cadlag semimartingale paired with an integrable-variation process
has an actual bracket of integrable variation. The proof identifies the
existing pure-jump bracket with a countably supported Stieltjes integral and
uses its quantitative variation bound. No martingale property or predictable
jump exhaustion is needed for this analytic statement.

The raw initial product is retained. It does not contribute to variation,
but initial integrability is separately supplied for the actual terminal
limit and Class D conclusion. This module does not prove Yoeurp's lemma.
-/

@[expose] public section

open MeasureTheory StochLean Filter Set Function
open scoped NNReal ENNReal Topology

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsFiniteMeasure P]
  {F : Filtration ℝ≥0 mΩ} {M A : ℝ≥0 → Ω → ℝ}

theorem IsSemimartingale.ae_eVariationOn_quadraticCovariation_le_of_finiteVariation_right
    (hM : IsSemimartingale M F P) (hA : IsSemimartingale A F P) (hF : F.IsUsual P)
    (hv : HasFiniteVariationPaths A P) {C : ℝ} (hC : 0 ≤ C)
    (hb : ∀ᵐ ω ∂P, ∀ t, ‖M t ω‖ ≤ C) :
    ∀ᵐ ω ∂P, eVariationOn (fun t ↦ hM.quadraticCovariation hA hF t ω) univ ≤
      ENNReal.ofReal (2 * C) * eVariationOn (A · ω) univ := by
  classical
  filter_upwards [hv, hA.hasCadlagPaths, hM.hasCadlagPaths, hb,
    hM.quadraticCovariation_of_finiteVariation_right hA hF hv]
      with ω hvω haω hmω hbω hq
  let g (t : ℝ≥0) : ℝ :=
    if A t ω - leftLim (A · ω) t = 0 then 0 else jumpProcess M t ω
  have hsupport : (support g).Countable :=
    (countable_support_jump_of_locallyBoundedVariation hvω haω.1).mono fun t ht ↦ by
      intro hz
      exact ht (by simp only [g, hz, if_true])
  have hg : Measurable g := by
    apply measurable_const.measurable_of_countable_ne (f := fun _ : ℝ≥0 ↦ (0 : ℝ))
    simpa only [ne_comm, support, mem_ofPred_eq] using hsupport
  have hgb (t : ℝ≥0) (ht : 0 < t) : ‖g t‖ ≤ 2 * C := by
    by_cases hz : A t ω - leftLim (A · ω) t = 0
    · simp only [g, hz, if_true, norm_zero]
      positivity
    · have hl : ‖leftLimitProcess M t ω‖ ≤ C := by
        let : (𝓝[<] t).NeBot := nhdsLT_neBot_of_exists_lt ⟨0, ht⟩
        exact le_of_tendsto (hmω.tendsto_leftLimitProcess ht.ne').norm
          (Eventually.of_forall hbω)
      simp only [g, hz, if_false]
      exact (norm_sub_le (M t ω) (leftLimitProcess M t ω)).trans
        ((add_le_add (hbω t) hl).trans_eq (two_mul C).symm)
  have hg0 : g 0 = 0 := by
    simp only [g, leftLim_eq_of_isBot (show IsBot (0 : ℝ≥0) from fun _ ↦ bot_le),
      sub_self, if_true]
  let I := pathStieltjesIntegral (A · ω) hvω haω.1 g
  have he (t : ℝ≥0) : hM.quadraticCovariation hA hF t ω = M 0 ω * A 0 ω + I t := by
    rw [hq t]
    change M 0 ω * A 0 ω + (∑' s : Ioc 0 t, jumpProcess M s ω * jumpProcess A s ω) =
      M 0 ω * A 0 ω + (g 0 * A 0 ω + pathStieltjesIncrementIntegral (A · ω) hvω haω.1 g 0 t)
    rw [hg0, zero_mul, zero_add,
      pathStieltjesIncrementIntegral_eq_tsum_of_countable_support hvω haω.1 t hg hsupport
        (fun s hs ↦ hgb s hs.1)]
    congr 1
    apply tsum_congr
    intro s
    have hja : jumpProcess A s ω = A s ω - leftLim (A · ω) s := by
      simp only [jumpProcess, Pi.sub_apply, leftLimitProcess, if_neg s.property.1.ne']
    rw [hja]
    by_cases hz : A s ω - leftLim (A · ω) s = 0
    · simp only [g, hz, if_true, mul_zero]
    · simp only [g, hz, if_false]
  have hev : eVariationOn (fun t ↦ hM.quadraticCovariation hA hF t ω) univ =
      eVariationOn I univ := by
    rw [eVariationOn.congr (fun t _ ↦ he t)]
    simp only [eVariationOn, edist_add_left]
  rw [hev]
  exact eVariationOn_pathStieltjesIntegral_univ_le hg (by positivity) hgb

theorem IsSemimartingale.hasIntegrableVariation_quadraticCovariation_of_right
    (hM : IsSemimartingale M F P) (hA : IsSemimartingale A F P) (hF : F.IsUsual P)
    (hv : HasIntegrableVariation A P) {C : ℝ} (hC : 0 ≤ C)
    (hb : ∀ᵐ ω ∂P, ∀ t, ‖M t ω‖ ≤ C) :
    HasIntegrableVariation (hM.quadraticCovariation hA hF) P := by
  have hbound := hM.ae_eVariationOn_quadraticCovariation_le_of_finiteVariation_right
    hA hF hv.hasFiniteVariationPaths hC hb
  have hfinite : ∀ᵐ ω ∂P,
      ENNReal.ofReal (2 * C) * eVariationOn (A · ω) univ ≠ ∞ :=
    hv.ae_eVariationOn_ne_top.mono fun _ hω ↦ ENNReal.mul_ne_top ENNReal.ofReal_ne_top hω
  constructor
  · filter_upwards [hbound, hfinite] with ω hω hf
    exact ne_top_of_le_ne_top hf hω
  · apply (hv.integrable_eVariationOn_toReal.const_mul (2 * C)).mono'
      (((hM.adapted_quadraticCovariation hA hF).measurable_eVariationOn_univ_of_usual hF
        (hM.hasCadlagPaths_quadraticCovariation hA hF)).ennreal_toReal).aestronglyMeasurable
    filter_upwards [hbound, hfinite] with ω hω hf
    rw [Real.norm_of_nonneg ENNReal.toReal_nonneg]
    have ht := ENNReal.toReal_mono hf hω
    simpa only [ENNReal.toReal_mul, ENNReal.toReal_ofReal (show 0 ≤ 2 * C by positivity)] using ht

/-- An integrable initial value of A controls the raw initial product; it
cannot be inferred from integrable variation alone. -/
theorem IsSemimartingale.exists_integrable_terminal_quadraticCovariation_of_right
    (hM : IsSemimartingale M F P) (hA : IsSemimartingale A F P) (hF : F.IsUsual P)
    (hv : HasIntegrableVariation A P) (hi0 : Integrable (A 0) P)
    {C : ℝ} (hC : 0 ≤ C) (hb : ∀ᵐ ω ∂P, ∀ t, ‖M t ω‖ ≤ C) :
    ∃ Z : Ω → ℝ, Integrable Z P ∧
      (∀ᵐ ω ∂P, Tendsto (fun t : ℝ≥0 ↦ hM.quadraticCovariation hA hF t ω)
        atTop (𝓝 (Z ω))) ∧
      Tendsto (fun t : ℝ≥0 ↦ eLpNorm (hM.quadraticCovariation hA hF t - Z) 1 P)
        atTop (𝓝 0) ∧ IsClassD (hM.quadraticCovariation hA hF) F P := by
  have hi : Integrable (fun ω ↦ M 0 ω * A 0 ω) P := by
    apply (hi0.norm.const_mul C).mono'
      (((hM.adapted 0).mono (F.le 0) le_rfl).aestronglyMeasurable.mul hi0.aestronglyMeasurable)
    filter_upwards [hb] with ω hω
    change ‖M 0 ω * A 0 ω‖ ≤ C * ‖A 0 ω‖
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_right (hω 0) (norm_nonneg _)
  have hiQ0 := hi.congr (hM.quadraticCovariation_zero_ae hA hF).symm
  have hqv := hM.hasIntegrableVariation_quadraticCovariation_of_right hA hF hv hC hb
  obtain ⟨Z, hiZ, hl, hL, hD, _, _⟩ :=
    hqv.exists_integrable_terminal (hM.adapted_quadraticCovariation hA hF) hF
      (hM.hasCadlagPaths_quadraticCovariation hA hF) hiQ0
  exact ⟨Z, hiZ, hl, hL, hD⟩

end ProbabilityTheory
