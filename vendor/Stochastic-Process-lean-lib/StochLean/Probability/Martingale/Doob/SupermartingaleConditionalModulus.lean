/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Martingale.Doob.ConditionalModulusPotential
public import StochLean.Probability.Martingale.Doob.ConditionalModulusVersions
public import StochLean.Probability.Martingale.Doob.TerminalPotential
public import StochLean.Probability.Martingale.Inequalities.NonnegativeSupermartingaleMaximal

/-! # Full bounded-supermartingale conditional modulus theorem

Protter III.10, Lemma 3, without requiring a finite terminal lifetime. In fact no
termination time, Class D premise or zero initial normalization is needed for the
bounded cadlag supermartingale theorem. The actual terminal potential controls late
increments, and its vanishing means make the future maximal probability tend to zero.
Early increments are controlled by the compact modulus at horizon `T + 1`.

This closes the conditional-modulus lemma, not the continuous Doob-Meyer construction.
The proof does not use a compensator or assume that the terminal potential has TI jumps.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsFiniteMeasure P]
  {F : Filtration ℝ≥0 mΩ} {X U : ℝ≥0 → Ω → ℝ} {N : ℝ}

theorem HasTotallyInaccessibleJumps.tendsto_globalConditionalModulus_of_potential
    (hJ : HasTotallyInaccessibleJumps F X P) (hF : F.IsUsual P) (hX : Adapted F X)
    (hc : HasCadlagPaths X P) (hN : 0 ≤ N) (hbound : ∀ᵐ ω ∂P, ∀ t, ‖X t ω‖ ≤ N)
    (hU : IsPotential U F P) (hr : HasRightContinuousPaths U P)
    (hinc : ∀ t u : ℝ≥0, t ≤ u → P[X t - X u | F t] ≤ᵐ[P] U t)
    {G : ℝ≥0 → Ω → ℝ≥0∞} (hG : ∀ δ, IsGlobalConditionalIncrementModulus F P X δ (G δ))
    {a : ℝ} (ha : 0 < a) :
    Tendsto (fun δ ↦ P.real {ω | ENNReal.ofReal a < G δ ω}) (𝓝 0) (𝓝 0) := by
  have hz : HasRightContinuousPaths (fun _ : ℝ≥0 ↦ (0 : Ω → ℝ)) P :=
    Eventually.of_forall fun _ _ ↦ continuousWithinAt_const
  have hn : ∀ᵐ ω ∂P, ∀ t, 0 ≤ U t ω :=
    hz.ae_forall_le_of_forall_ae_le hr hU.nonneg
  have hi (t : ℝ≥0) : Integrable (X t) P :=
    (MemLp.of_bound ((hX t).mono (F.le t) le_rfl).aestronglyMeasurable N
      (hbound.mono fun _ hω ↦ hω t) (p := 1)).integrable le_rfl
  have htail : Tendsto (fun T : ℝ≥0 ↦ (3 * ∫ ω, U T ω ∂P) / (a / 2)) atTop (𝓝 0) := by
    simpa only [mul_zero, zero_div] using
      (hU.tendsto_integral.const_mul 3).div_const (a / 2)
  refine tendsto_order.mpr ⟨?_, ?_⟩
  · intro z hz
    exact Eventually.of_forall fun _ ↦ hz.trans_le measureReal_nonneg
  · intro z hz
    obtain ⟨T, hT⟩ := (htail.eventually_lt_const (half_pos hz)).exists
    choose W hW using fun δ ↦ exists_conditionalIncrementModulus F P X (T + 1) δ
    have hfin (δ : ℝ≥0) : ∀ᵐ ω ∂P, W δ ω ≠ ∞ :=
      (hW δ).ae_ne_top_of_norm_bound (fun t _ ↦ hi t)
        (fun t _ ↦ hbound.mono fun _ hω ↦ hω t)
    have hwreal := (hJ.tendstoInMeasure_conditionalModulus_of_hasCadlagPaths hF hX hc hN
      hbound hW).tendsto_measureReal_gt_zero (half_pos ha)
    have hweq (δ : ℝ≥0) : P.real {ω | a / 2 < (W δ ω).toReal} =
        P.real {ω | ENNReal.ofReal (a / 2) < W δ ω} := by
      apply congrArg ENNReal.toReal
      apply measure_congr
      filter_upwards [hfin δ] with ω hω
      exact propext (ENNReal.ofReal_lt_iff_lt_toReal (half_pos ha).le hω).symm
    have hw : Tendsto (fun δ ↦ P.real {ω | ENNReal.ofReal (a / 2) < W δ ω})
        (𝓝 0) (𝓝 0) := hwreal.congr' (Eventually.of_forall hweq)
    have hu := hU.supermartingale.measureReal_exists_future_gt_le_three_of_nonneg
      hn hr T (half_pos ha)
    filter_upwards [hw.eventually_lt_const (half_pos hz),
      Iio_mem_nhds (show (0 : ℝ≥0) < 1 from zero_lt_one)] with δ hwδ hδ
    have hs := (hG δ).measureReal_gt_le_compact_add_potential_tail (hW δ) hδ.le hinc ha
    linarith only [hs, hu, hT, hwδ]

end ProbabilityTheory

namespace MeasureTheory.Supermartingale

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsFiniteMeasure P]
  {F : Filtration ℝ≥0 mΩ} {X : ℝ≥0 → Ω → ℝ} {N : ℝ}

theorem tendsto_measureReal_globalConditionalModulus_of_bound
    (hX : Supermartingale X F P) (hF : F.IsUsual P) (hc : HasCadlagPaths X P)
    (hJ : HasTotallyInaccessibleJumps F X P) (hN : 0 ≤ N)
    (hbound : ∀ᵐ ω ∂P, ∀ t, ‖X t ω‖ ≤ N)
    {G : ℝ≥0 → Ω → ℝ≥0∞} (hG : ∀ δ, IsGlobalConditionalIncrementModulus F P X δ (G δ))
    {a : ℝ} (ha : 0 < a) :
    Tendsto (fun δ ↦ P.real {ω | ENNReal.ofReal a < G δ ω}) (𝓝 0) (𝓝 0) := by
  obtain ⟨Z, M, _, _, _, _, _, _, _, hU, hcU, _, hinc⟩ :=
    hX.exists_bounded_terminal_potential hF hc hN hbound
  exact hJ.tendsto_globalConditionalModulus_of_potential hF hX.stronglyAdapted.adapted
    hc hN hbound hU hcU.hasRightContinuousPaths hinc hG ha

theorem tendstoInMeasure_globalConditionalModulus_of_bound
    (hX : Supermartingale X F P) (hF : F.IsUsual P) (hc : HasCadlagPaths X P)
    (hJ : HasTotallyInaccessibleJumps F X P) (hN : 0 ≤ N)
    (hbound : ∀ᵐ ω ∂P, ∀ t, ‖X t ω‖ ≤ N)
    {G : ℝ≥0 → Ω → ℝ≥0∞} (hG : ∀ δ, IsGlobalConditionalIncrementModulus F P X δ (G δ)) :
    TendstoInMeasure P (fun δ ω ↦ (G δ ω).toReal) (𝓝 0) (fun _ ↦ (0 : ℝ)) := by
  apply tendstoInMeasure_zero_of_nonneg_of_measureReal_gt
    (fun _ ↦ Eventually.of_forall fun _ ↦ ENNReal.toReal_nonneg)
  intro a ha
  have hfin (δ : ℝ≥0) : ∀ᵐ ω ∂P, G δ ω ≠ ∞ :=
    (hG δ).ae_ne_top_of_norm_bound hX.integrable (fun t ↦ hbound.mono fun _ hω ↦ hω t)
  have he (δ : ℝ≥0) : P.real {ω | ENNReal.ofReal a < G δ ω} =
      P.real {ω | a < (G δ ω).toReal} := by
    apply congrArg ENNReal.toReal
    apply measure_congr
    filter_upwards [hfin δ] with ω hω
    exact propext (ENNReal.ofReal_lt_iff_lt_toReal ha.le hω)
  exact (hX.tendsto_measureReal_globalConditionalModulus_of_bound hF hc hJ hN hbound hG ha).congr'
    (Eventually.of_forall he)

theorem globalConditionalModulus_L2_convergence_of_bound
    (hX : Supermartingale X F P) (hF : F.IsUsual P) (hc : HasCadlagPaths X P)
    (hJ : HasTotallyInaccessibleJumps F X P) (hN : 0 ≤ N)
    (hbound : ∀ᵐ ω ∂P, ∀ t, ‖X t ω‖ ≤ N)
    {G : ℝ≥0 → Ω → ℝ≥0∞} (hG : ∀ δ, IsGlobalConditionalIncrementModulus F P X δ (G δ)) :
    (∀ δ, MemLp (fun ω ↦ (G δ ω).toReal) 2 P) ∧
      Tendsto (fun δ ↦ ∫ ω, (G δ ω).toReal ^ 2 ∂P) (𝓝 0) (𝓝 0) ∧
        Tendsto (fun δ ↦ eLpNorm (fun ω ↦ (G δ ω).toReal) 2 P) (𝓝 0) (𝓝 0) := by
  have hC : 0 ≤ 2 * N := mul_nonneg (by norm_num) hN
  have hm (δ : ℝ≥0) : AEStronglyMeasurable (fun ω ↦ (G δ ω).toReal) P :=
    (hG δ).measurable.ennreal_toReal.aestronglyMeasurable
  have hb (δ : ℝ≥0) : ∀ᵐ ω ∂P, ‖(G δ ω).toReal‖ ≤ 2 * N := by
    filter_upwards [(hG δ).ae_le_of_norm_bound hX.integrable
      (fun t ↦ hbound.mono fun _ hω ↦ hω t)] with ω hω
    rw [Real.norm_of_nonneg ENNReal.toReal_nonneg]
    simpa only [ENNReal.toReal_ofReal hC] using ENNReal.toReal_mono ENNReal.ofReal_ne_top hω
  have hl := hX.tendstoInMeasure_globalConditionalModulus_of_bound hF hc hJ hN hbound hG
  exact ⟨fun δ ↦ MemLp.of_bound (hm δ) (2 * N) (hb δ),
    hl.tendsto_integral_sq_of_bound hm hC hb, hl.tendsto_eLpNorm_two_of_bound hm hC hb⟩

/-- Existence and full global L2 convergence on the bounded-supermartingale source domain.
No termination time, modulus, compensator, or convergence certificate is supplied. -/
theorem exists_globalConditionalModulus_L2_convergence_of_bound
    (hX : Supermartingale X F P) (hF : F.IsUsual P) (hc : HasCadlagPaths X P)
    (hJ : HasTotallyInaccessibleJumps F X P) (hN : 0 ≤ N)
    (hbound : ∀ᵐ ω ∂P, ∀ t, ‖X t ω‖ ≤ N) :
    ∃ G : ℝ≥0 → Ω → ℝ≥0∞, (∀ δ, IsGlobalConditionalIncrementModulus F P X δ (G δ)) ∧
      TendstoInMeasure P (fun δ ω ↦ (G δ ω).toReal) (𝓝 0) (fun _ ↦ (0 : ℝ)) ∧
        (∀ δ, MemLp (fun ω ↦ (G δ ω).toReal) 2 P) ∧
          Tendsto (fun δ ↦ ∫ ω, (G δ ω).toReal ^ 2 ∂P) (𝓝 0) (𝓝 0) ∧
            Tendsto (fun δ ↦ eLpNorm (fun ω ↦ (G δ ω).toReal) 2 P) (𝓝 0) (𝓝 0) := by
  choose G hG using fun δ ↦ exists_globalConditionalIncrementModulus F P X δ
  exact ⟨G, hG, hX.tendstoInMeasure_globalConditionalModulus_of_bound hF hc hJ hN hbound hG,
    hX.globalConditionalModulus_L2_convergence_of_bound hF hc hJ hN hbound hG⟩

end MeasureTheory.Supermartingale
