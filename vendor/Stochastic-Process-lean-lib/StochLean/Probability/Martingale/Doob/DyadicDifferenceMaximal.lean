/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Martingale.Doob.DyadicTerminalEnergy
public import StochLean.Probability.Martingale.Doob.DyadicStepRegularity
public import StochLean.Probability.Martingale.Doob.PredictableDifferenceMaximal

/-! # Actual maximal bounds for two dyadic Doob approximants

The actual terminal identities supply the conditional remaining-difference bound.
A common finer grid recovers both left-step processes exactly, so the countable
maximal estimate controls all real times. No ordering of the two mesh indices is
required. Modulus integrability, the countable value representation, and the
maximal envelope are derived, rather than supplied as certificate hypotheses.
-/

@[expose] public section

open ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology

namespace MeasureTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsFiniteMeasure P]
  {F : Filtration ℝ≥0 mΩ} {X : ℝ≥0 → Ω → ℝ} {Z U V : Ω → ℝ} {N : ℝ}
  {G H : Ω → ℝ≥0∞}

private theorem memLp_two_modulus_of_uniform_bound (hX : Supermartingale X F P)
    (hN : 0 ≤ N) (hb : ∀ t, ∀ᵐ ω ∂P, ‖X t ω‖ ≤ N) {δ : ℝ≥0}
    (hG : IsGlobalConditionalIncrementModulus F P X δ G) :
    MemLp (fun ω ↦ (G ω).toReal) 2 P := by
  have hC : 0 ≤ 2 * N := mul_nonneg (by norm_num) hN
  apply MemLp.of_bound hG.measurable.ennreal_toReal.aestronglyMeasurable (2 * N)
  filter_upwards [hG.ae_le_of_norm_bound hX.integrable hb] with ω hω
  rw [Real.norm_of_nonneg ENNReal.toReal_nonneg]
  simpa only [ENNReal.toReal_ofReal hC] using
    ENNReal.toReal_mono ENNReal.ofReal_ne_top hω

/-- An actual global L2 envelope for the difference of two native dyadic steps.
The input terminals must be the actual fixed-mesh limits. No maximal or Cauchy
estimate, and no countable-cover certificate, is assumed. -/
theorem Supermartingale.exists_memLp_two_dyadicDoob_difference_globalEnvelope
    (hX : Supermartingale X F P) (hF : F.IsUsual P) (n m : ℕ)
    (hN : 0 ≤ N) (hb : ∀ t, ∀ᵐ ω ∂P, ‖X t ω‖ ≤ N)
    (hZ : Integrable Z P) (hU : MemLp U 2 P) (hV : MemLp V 2 P)
    (hlZ : ∀ᵐ ω ∂P, Tendsto (fun t : ℝ≥0 ↦ X t ω) atTop (𝓝 (Z ω)))
    (hlU : ∀ᵐ ω ∂P,
      Tendsto (fun k ↦ dyadicDoobIncreasing X F P n k ω) atTop (𝓝 (U ω)))
    (hlV : ∀ᵐ ω ∂P,
      Tendsto (fun k ↦ dyadicDoobIncreasing X F P m k ω) atTop (𝓝 (V ω)))
    (hG : IsGlobalConditionalIncrementModulus F P X (1 / ((2 ^ n : ℕ) : ℝ≥0)) G)
    (hH : IsGlobalConditionalIncrementModulus F P X (1 / ((2 ^ m : ℕ) : ℝ≥0)) H) :
    ∃ g : Ω → ℝ, Measurable g ∧ (∀ ω, 0 ≤ g ω) ∧ MemLp g 2 P ∧
      (∀ᵐ ω ∂P, ∀ t : ℝ≥0,
        ‖dyadicDoobStep X F P n t ω - dyadicDoobStep X F P m t ω‖ ≤ g ω) ∧
      (∫ ω, g ω ^ 2 ∂P) ≤ 8 * ((∫ ω, (U ω - V ω) ^ 2 ∂P) +
        ∫ ω, ((G ω).toReal + (H ω).toReal) ^ 2 ∂P) := by
  let r : ℕ := max n m
  let e (k : ℕ) : ℝ≥0 := (k : ℝ≥0) / (2 ^ r : ℕ)
  let C (k : ℕ) : Ω → ℝ := dyadicDoobStep X F P n (e k) - dyadicDoobStep X F P m (e k)
  have hG2 := memLp_two_modulus_of_uniform_bound hX hN hb hG
  have hH2 := memLp_two_modulus_of_uniform_bound hX hN hb hH
  have hmC (k : ℕ) : StronglyMeasurable[F (e k)] (C k) :=
    (dyadicDoobStep_stronglyAdapted X F P n (e k)).sub
      (dyadicDoobStep_stronglyAdapted X F P m (e k))
  have hiC (k : ℕ) : Integrable (C k) P :=
    (dyadicDoobStep_integrable X F P n (e k)).sub
      (dyadicDoobStep_integrable X F P m (e k))
  have htail (k : ℕ) : ∀ᵐ ω ∂P,
      ‖P[(U - V) - C k | F (e k)] ω‖ ≤
        P[(fun ω ↦ (G ω).toReal + (H ω).toReal) | F (e k)] ω := by
    have he : (U - V) - C k =
        (U - dyadicDoobStep X F P n (e k)) -
          (V - dyadicDoobStep X F P m (e k)) := by
      funext ω
      simp only [C, Pi.sub_apply]
      ring
    rw [he]
    exact hX.norm_condExp_dyadicDoob_terminal_difference_le_moduli n m hb hZ hU hV
      hlZ hlU hlV hG hH (hG2.integrable (by norm_num)) (hH2.integrable (by norm_num)) (e k)
  obtain ⟨g, hgm, hgn, hgL, hgb, hgE⟩ :=
    exists_memLp_two_countable_condExp_tail_envelope hF (hU.sub hV) (hG2.add hH2)
      hmC hiC htail
  have hrecover (t : ℝ≥0) : C (Nat.ceil (((2 ^ r : ℕ) : ℝ≥0) * t)) =
      dyadicDoobStep X F P n t - dyadicDoobStep X F P m t := by
    have hnr : n ≤ r := le_max_left n m
    have hmr : m ≤ r := le_max_right n m
    have he : e (Nat.ceil (((2 ^ r : ℕ) : ℝ≥0) * t)) = dyadicRightGrid r t :=
      dyadicDoobStep_grid_time r t
    simp only [C, he, dyadicDoobStep_finer_rightGrid X F P hnr t,
      dyadicDoobStep_finer_rightGrid X F P hmr t]
  refine ⟨g, hgm, hgn, hgL, ?_, ?_⟩
  · filter_upwards [hgb] with ω hω t
    simpa only [hrecover t, Pi.sub_apply] using
      hω (Nat.ceil (((2 ^ r : ℕ) : ℝ≥0) * t))
  · simpa only [Pi.sub_apply, Pi.add_apply] using hgE

/-- The actual whole-half-line exceedance probability is controlled by terminal
energy and the two moduli. The process difference need not be right continuous. -/
theorem Supermartingale.measureReal_exists_dyadicDoob_difference_gt_le
    (hX : Supermartingale X F P) (hF : F.IsUsual P) (n m : ℕ)
    (hN : 0 ≤ N) (hb : ∀ t, ∀ᵐ ω ∂P, ‖X t ω‖ ≤ N)
    (hZ : Integrable Z P) (hU : MemLp U 2 P) (hV : MemLp V 2 P)
    (hlZ : ∀ᵐ ω ∂P, Tendsto (fun t : ℝ≥0 ↦ X t ω) atTop (𝓝 (Z ω)))
    (hlU : ∀ᵐ ω ∂P,
      Tendsto (fun k ↦ dyadicDoobIncreasing X F P n k ω) atTop (𝓝 (U ω)))
    (hlV : ∀ᵐ ω ∂P,
      Tendsto (fun k ↦ dyadicDoobIncreasing X F P m k ω) atTop (𝓝 (V ω)))
    (hG : IsGlobalConditionalIncrementModulus F P X (1 / ((2 ^ n : ℕ) : ℝ≥0)) G)
    (hH : IsGlobalConditionalIncrementModulus F P X (1 / ((2 ^ m : ℕ) : ℝ≥0)) H)
    {a : ℝ} (ha : 0 < a) :
    P.real {ω | ∃ t : ℝ≥0,
      a < ‖dyadicDoobStep X F P n t ω - dyadicDoobStep X F P m t ω‖} ≤
        8 * ((∫ ω, (U ω - V ω) ^ 2 ∂P) +
          ∫ ω, ((G ω).toReal + (H ω).toReal) ^ 2 ∂P) / a ^ 2 := by
  obtain ⟨g, _, _, hgL, hgb, hgE⟩ :=
    hX.exists_memLp_two_dyadicDoob_difference_globalEnvelope hF n m hN hb hZ hU hV
      hlZ hlU hlV hG hH
  have hsub : P {ω | ∃ t : ℝ≥0,
      a < ‖dyadicDoobStep X F P n t ω - dyadicDoobStep X F P m t ω‖} ≤
        P {ω | a ≤ ‖g ω‖} := by
    apply measure_mono_ae
    filter_upwards [hgb] with ω hω htω
    obtain ⟨t, ht⟩ := htω
    exact (ht.le.trans (hω t)).trans (le_abs_self _)
  have hmarkov := measure_norm_ge_le_integral_sq_div hgL.integrable_sq ha
  have hreal : P.real {ω | a ≤ ‖g ω‖} ≤ (∫ ω, g ω ^ 2 ∂P) / a ^ 2 := by
    rw [Measure.real]
    simpa only [ENNReal.toReal_ofReal (div_nonneg
      (integral_nonneg fun ω ↦ sq_nonneg _) (sq_nonneg a))] using
      ENNReal.toReal_mono ENNReal.ofReal_ne_top hmarkov
  exact (ENNReal.toReal_mono (measure_ne_top _ _) hsub).trans
    (hreal.trans (div_le_div_of_nonneg_right hgE (sq_nonneg a)))

theorem Supermartingale.measureReal_exists_compact_dyadicDoob_difference_gt_le
    (hX : Supermartingale X F P) (hF : F.IsUsual P) (n m : ℕ)
    (hN : 0 ≤ N) (hb : ∀ t, ∀ᵐ ω ∂P, ‖X t ω‖ ≤ N)
    (hZ : Integrable Z P) (hU : MemLp U 2 P) (hV : MemLp V 2 P)
    (hlZ : ∀ᵐ ω ∂P, Tendsto (fun t : ℝ≥0 ↦ X t ω) atTop (𝓝 (Z ω)))
    (hlU : ∀ᵐ ω ∂P,
      Tendsto (fun k ↦ dyadicDoobIncreasing X F P n k ω) atTop (𝓝 (U ω)))
    (hlV : ∀ᵐ ω ∂P,
      Tendsto (fun k ↦ dyadicDoobIncreasing X F P m k ω) atTop (𝓝 (V ω)))
    (hG : IsGlobalConditionalIncrementModulus F P X (1 / ((2 ^ n : ℕ) : ℝ≥0)) G)
    (hH : IsGlobalConditionalIncrementModulus F P X (1 / ((2 ^ m : ℕ) : ℝ≥0)) H)
    (T : ℝ≥0) {a : ℝ} (ha : 0 < a) :
    P.real {ω | ∃ t ≤ T,
      a < ‖dyadicDoobStep X F P n t ω - dyadicDoobStep X F P m t ω‖} ≤
        8 * ((∫ ω, (U ω - V ω) ^ 2 ∂P) +
          ∫ ω, ((G ω).toReal + (H ω).toReal) ^ 2 ∂P) / a ^ 2 := by
  apply le_trans _ (hX.measureReal_exists_dyadicDoob_difference_gt_le
    hF n m hN hb hZ hU hV hlZ hlU hlV hG hH ha)
  apply ENNReal.toReal_mono (measure_ne_top _ _)
  exact measure_mono fun _ ⟨t, _, ht⟩ ↦ ⟨t, ht⟩

end MeasureTheory
