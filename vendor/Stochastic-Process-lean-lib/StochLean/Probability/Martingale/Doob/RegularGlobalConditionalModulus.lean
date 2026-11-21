/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Martingale.Doob.RegularConditionalModulus
public import StochLean.Probability.Martingale.Doob.ConditionalModulusPotential
public import StochLean.Probability.Martingale.Doob.TerminalPotential
public import StochLean.Probability.Martingale.Inequalities.NonnegativeSupermartingaleMaximal
public import StochLean.ForMathlib.MeasureTheory.Function.BoundedMomentConvergence

/-! # Global signed conditional moduli under predictable jump mean regularity

The actual terminal limit and its conditional martingale construct a
nonnegative potential internally. Vanishing potential means control all
late increments by the existing supermartingale maximal inequality. Early
increments use the regular compact-modulus theorem on horizon `T + 1`.

Boundedness upgrades probability convergence to both square-integral and
native L2 convergence. No terminal lifetime, compensator, candidate potential,
TI jump hypothesis, or assumed modulus convergence is supplied. Arbitrary
initial values are retained, and extended moduli are proved finite before
their real values enter the convergence assertions.
-/

@[expose] public section

open ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology

namespace MeasureTheory.Supermartingale

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsFiniteMeasure P]
  {F : Filtration ℝ≥0 mΩ} {X : ℝ≥0 → Ω → ℝ} {N : ℝ}

/-- Compact regularity and the internally constructed terminal potential
control the actual global modulus on the whole half-line. -/
theorem tendsto_measureReal_globalConditionalModulus_of_predictable_jump_mean_zero
    (hX : Supermartingale X F P) (hF : F.IsUsual P) (hc : HasCadlagPaths X P)
    (hN : 0 ≤ N) (hb : ∀ᵐ ω ∂P, ∀ t, ‖X t ω‖ ≤ N)
    (hreg : ∀ (ρ : Ω → WithTop ℝ≥0), IsPredictableStoppingTime F ρ P →
      (∀ᵐ ω ∂P, 0 < ρ ω) →
      (∫ ω, stoppedValueWithTerminal (jumpProcess X) (fun _ ↦ (0 : ℝ)) ρ ω ∂P) = 0)
    {G : ℝ≥0 → Ω → ℝ≥0∞}
    (hG : ∀ δ, IsGlobalConditionalIncrementModulus F P X δ (G δ))
    {a : ℝ} (ha : 0 < a) :
    Tendsto (fun δ ↦ P.real {ω | ENNReal.ofReal a < G δ ω}) (𝓝 0) (𝓝 0) := by
  obtain ⟨_, M, _, _, _, _, _, _, _, hU, hcU, hbU, hinc⟩ :=
    hX.exists_bounded_terminal_potential hF hc hN hb
  have hn : ∀ᵐ ω ∂P, ∀ t, 0 ≤ (X - M) t ω :=
    hbU.mono fun _ hω t ↦ (hω t).1
  have htail : Tendsto (fun T : ℝ≥0 ↦ (3 * ∫ ω, (X - M) T ω ∂P) / (a / 2))
      atTop (𝓝 0) := by
    simpa only [mul_zero, zero_div] using
      (hU.tendsto_integral.const_mul 3).div_const (a / 2)
  refine tendsto_order.mpr ⟨?_, ?_⟩
  · intro z hz
    exact Eventually.of_forall fun _ ↦ hz.trans_le measureReal_nonneg
  · intro z hz
    obtain ⟨T, hT⟩ := (htail.eventually_lt_const (half_pos hz)).exists
    choose W hW using fun δ ↦ exists_conditionalIncrementModulus F P X (T + 1) δ
    have hw := hX.tendsto_measureReal_conditionalModulus_of_predictable_jump_mean_zero
      hF hc hN hb hreg hW (half_pos ha)
    have hu := hU.supermartingale.measureReal_exists_future_gt_le_three_of_nonneg
      hn hcU.hasRightContinuousPaths T (half_pos ha)
    filter_upwards [hw.eventually_lt_const (half_pos hz),
      Iio_mem_nhds (show (0 : ℝ≥0) < 1 from zero_lt_one)] with δ hwδ hδ
    have hs := (hG δ).measureReal_gt_le_compact_add_potential_tail (hW δ) hδ.le hinc ha
    linarith only [hs, hu, hT, hwδ]

/-- Every version of the actual finite global modulus converges in measure. -/
theorem tendstoInMeasure_globalConditionalModulus_of_predictable_jump_mean_zero
    (hX : Supermartingale X F P) (hF : F.IsUsual P) (hc : HasCadlagPaths X P)
    (hN : 0 ≤ N) (hb : ∀ᵐ ω ∂P, ∀ t, ‖X t ω‖ ≤ N)
    (hreg : ∀ (ρ : Ω → WithTop ℝ≥0), IsPredictableStoppingTime F ρ P →
      (∀ᵐ ω ∂P, 0 < ρ ω) →
      (∫ ω, stoppedValueWithTerminal (jumpProcess X) (fun _ ↦ (0 : ℝ)) ρ ω ∂P) = 0)
    {G : ℝ≥0 → Ω → ℝ≥0∞}
    (hG : ∀ δ, IsGlobalConditionalIncrementModulus F P X δ (G δ)) :
    TendstoInMeasure P (fun δ ω ↦ (G δ ω).toReal) (𝓝 0) (fun _ ↦ (0 : ℝ)) := by
  apply tendstoInMeasure_zero_of_nonneg_of_measureReal_gt
    (fun _ ↦ Eventually.of_forall fun _ ↦ ENNReal.toReal_nonneg)
  intro a ha
  have hfin (δ : ℝ≥0) : ∀ᵐ ω ∂P, G δ ω ≠ ∞ :=
    (hG δ).ae_ne_top_of_norm_bound hX.integrable (fun t ↦ hb.mono fun _ hω ↦ hω t)
  have he (δ : ℝ≥0) : P.real {ω | ENNReal.ofReal a < G δ ω} =
      P.real {ω | a < (G δ ω).toReal} := by
    apply measureReal_congr
    filter_upwards [hfin δ] with ω hω
    exact propext (ENNReal.ofReal_lt_iff_lt_toReal ha.le hω)
  exact (hX.tendsto_measureReal_globalConditionalModulus_of_predictable_jump_mean_zero
    hF hc hN hb hreg hG ha).congr' (Eventually.of_forall he)

/-- The deterministic source bound gives uniform L2 domination, after
actual extended-modulus finiteness has been established. -/
theorem globalConditionalModulus_L2_convergence_of_predictable_jump_mean_zero
    (hX : Supermartingale X F P) (hF : F.IsUsual P) (hc : HasCadlagPaths X P)
    (hN : 0 ≤ N) (hb : ∀ᵐ ω ∂P, ∀ t, ‖X t ω‖ ≤ N)
    (hreg : ∀ (ρ : Ω → WithTop ℝ≥0), IsPredictableStoppingTime F ρ P →
      (∀ᵐ ω ∂P, 0 < ρ ω) →
      (∫ ω, stoppedValueWithTerminal (jumpProcess X) (fun _ ↦ (0 : ℝ)) ρ ω ∂P) = 0)
    {G : ℝ≥0 → Ω → ℝ≥0∞}
    (hG : ∀ δ, IsGlobalConditionalIncrementModulus F P X δ (G δ)) :
    (∀ δ, MemLp (fun ω ↦ (G δ ω).toReal) 2 P) ∧
      Tendsto (fun δ ↦ ∫ ω, (G δ ω).toReal ^ 2 ∂P) (𝓝 0) (𝓝 0) ∧
        Tendsto (fun δ ↦ eLpNorm (fun ω ↦ (G δ ω).toReal) 2 P) (𝓝 0) (𝓝 0) := by
  have hC : 0 ≤ 2 * N := mul_nonneg (by norm_num) hN
  have hm (δ : ℝ≥0) : AEStronglyMeasurable (fun ω ↦ (G δ ω).toReal) P :=
    (hG δ).measurable.ennreal_toReal.aestronglyMeasurable
  have hbound (δ : ℝ≥0) : ∀ᵐ ω ∂P, ‖(G δ ω).toReal‖ ≤ 2 * N := by
    filter_upwards [(hG δ).ae_le_of_norm_bound hX.integrable
      (fun t ↦ hb.mono fun _ hω ↦ hω t)] with ω hω
    rw [Real.norm_of_nonneg ENNReal.toReal_nonneg]
    simpa only [ENNReal.toReal_ofReal hC] using ENNReal.toReal_mono ENNReal.ofReal_ne_top hω
  have hl := hX.tendstoInMeasure_globalConditionalModulus_of_predictable_jump_mean_zero
    hF hc hN hb hreg hG
  exact ⟨fun δ ↦ MemLp.of_bound (hm δ) (2 * N) (hbound δ),
    hl.tendsto_integral_sq_of_bound hm hC hbound,
    hl.tendsto_eLpNorm_two_of_bound hm hC hbound⟩

/-- Actual existence and global convergence on the bounded regular source
domain, with no modulus or convergence certificate supplied by the caller. -/
theorem exists_globalConditionalModulus_L2_convergence_of_predictable_jump_mean_zero
    (hX : Supermartingale X F P) (hF : F.IsUsual P) (hc : HasCadlagPaths X P)
    (hN : 0 ≤ N) (hb : ∀ᵐ ω ∂P, ∀ t, ‖X t ω‖ ≤ N)
    (hreg : ∀ (ρ : Ω → WithTop ℝ≥0), IsPredictableStoppingTime F ρ P →
      (∀ᵐ ω ∂P, 0 < ρ ω) →
      (∫ ω, stoppedValueWithTerminal (jumpProcess X) (fun _ ↦ (0 : ℝ)) ρ ω ∂P) = 0) :
    ∃ G : ℝ≥0 → Ω → ℝ≥0∞,
      (∀ δ, IsGlobalConditionalIncrementModulus F P X δ (G δ)) ∧
      TendstoInMeasure P (fun δ ω ↦ (G δ ω).toReal) (𝓝 0) (fun _ ↦ (0 : ℝ)) ∧
      (∀ δ, MemLp (fun ω ↦ (G δ ω).toReal) 2 P) ∧
      Tendsto (fun δ ↦ ∫ ω, (G δ ω).toReal ^ 2 ∂P) (𝓝 0) (𝓝 0) ∧
      Tendsto (fun δ ↦ eLpNorm (fun ω ↦ (G δ ω).toReal) 2 P) (𝓝 0) (𝓝 0) := by
  choose G hG using fun δ ↦ exists_globalConditionalIncrementModulus F P X δ
  exact ⟨G, hG,
    hX.tendstoInMeasure_globalConditionalModulus_of_predictable_jump_mean_zero hF hc hN hb hreg hG,
    hX.globalConditionalModulus_L2_convergence_of_predictable_jump_mean_zero hF hc hN hb hreg hG⟩

end MeasureTheory.Supermartingale
