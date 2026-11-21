/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Martingale.Doob.ConditionalModulusResidual
public import StochLean.Probability.Martingale.Doob.ConditionalEnvelope
public import StochLean.Probability.Process.Stopping.ConditionalWindowLimit
public import StochLean.ForMathlib.MeasureTheory.Function.FiniteTailBounds

/-! # Actual small-window tail estimates for the conditional modulus

For a fixed jump threshold and a fixed finite prefix, the conditional residual envelope
is constructed by martingale regularization. Doob's inequality controls its maximum.
Each of the finitely many removed jumps is totally inaccessible, so its conditional
window maximum tends to zero. The resulting estimate uses the actual coverage event
and actual residual moments, not a supplied decomposition or a jump-count moment.
-/

@[expose] public section

open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsFiniteMeasure P]
  {F : Filtration ℝ≥0 mΩ} {X : ℝ≥0 → Ω → ℝ} {N b : ℝ} {T : ℝ≥0}

theorem HasTotallyInaccessibleJumps.eventually_measureReal_conditionalModulus_gt_le
    (hJ : HasTotallyInaccessibleJumps F X P) (hF : F.IsUsual P) (hX : Adapted F X)
    (hc : ∀ ω, IsCadlagPath (X · ω)) (hN : 0 ≤ N)
    (hbound : ∀ᵐ ω ∂P, ∀ t, ‖X t ω‖ ≤ N) (hb : 0 < b) (K : ℕ)
    {δ : ℕ → ℝ≥0} (hδ : Tendsto δ atTop (𝓝 0)) (hδpos : ∀ n, 0 < δ n)
    {W : ℕ → Ω → ℝ≥0∞} (hW : ∀ n, IsConditionalIncrementModulus F P X T (δ n) (W n))
    {a ε : ℝ} (ha : 0 < a) (hε : 0 < ε) :
    ∀ᶠ n in atTop, P.real {ω | a < (W n ω).toReal} ≤
      4 * (b ^ 2 * P.real (largeJumpCoverageEvent X b T K) +
        (2 * N) ^ 2 * P.real (largeJumpCoverageEvent X b T K)ᶜ + ε) / (a / 2) ^ 2 + ε := by
  classical
  let : F.IsRightContinuous := hF.rightContinuous
  have hC : 0 ≤ 2 * N := mul_nonneg (by norm_num) hN
  let D : ℕ → Ω → ℝ := fun n ↦
    cappedDenseWindowOscillation (largeJumpResidual X b K) T (2 * δ n) (2 * N)
  have hD (n : ℕ) : MemLp (D n) 2 P :=
    hX.memLp_capped_largeJumpResidual_window hc hb T (2 * δ n) K hC
  have hnD (n : ℕ) : 0 ≤ᵐ[P] D n := Eventually.of_forall fun ω ↦
    cappedDenseWindowOscillation_nonneg (largeJumpResidual X b K) T (2 * δ n) hC ω
  choose M hM hcM heM hnM hmax using fun n ↦ exists_cadlag_conditionalEnvelope hF (hD n) (hnD n)
  have hτ (i : ℕ) := hJ.isTotallyInaccessibleStoppingTime_largeJumpSequence hX hc hb i
  choose R haR hcR heR hbR using fun (i : ℕ) (d : ℝ≥0) ↦
    (hτ i).1.exists_cadlag_conditional_window hF d
  let q : ℝ := a / (2 * (2 * N * (Finset.range K).card + 1))
  have hq : 0 < q := by dsimp [q]; positivity
  have hRlim (i : ℕ) : Tendsto
      (fun n ↦ P.real {ω | q < (denseRunningSupremum (R i (δ n)) T ω).toReal})
      atTop (𝓝 0) := by
    exact ((hτ i).tendstoInMeasure_conditional_window_supremum hF
      (fun d ↦ (hcR i d).hasRightContinuousPaths) (heR i) T).tendsto_measureReal_gt_zero hq
      |>.comp hδ
  have hsum : Tendsto
      (fun n ↦ ∑ i ∈ Finset.range K,
        P.real {ω | q < (denseRunningSupremum (R i (δ n)) T ω).toReal}) atTop (𝓝 0) := by
    simpa only [Finset.sum_const_zero] using
      (tendsto_finsetSum (Finset.range K) (fun i _ ↦ hRlim i))
  have htwice : Tendsto (fun n ↦ 2 * δ n) atTop (𝓝 0) := by
    simpa only [mul_zero] using tendsto_const_nhds.mul hδ
  have hmom := hX.eventually_integral_sq_largeJumpResidual_window_le
    (P := P) hc hb T K hC htwice hε
  filter_upwards [hmom, hsum.eventually_lt_const hε] with n hmoment hsmall
  have hdom := (hW n).ae_bounds_of_largeJumpResidual hX hc hb hN hbound K (hδpos n)
    (M n) (fun i ↦ R i (δ n)) (hcM n).hasRightContinuousPaths
    (fun i _ ↦ (hcR i (δ n)).hasRightContinuousPaths) (heM n)
    (fun i _ ↦ heR i (δ n))
  have hsplit := measureReal_gt_le_of_ae_le_add_finset_mul (Finset.range K) hC ha
    (hdom.mono fun _ hω ↦ hω.2.2)
  have hmaxbound := ((hmax n T).2 (a / 2) (half_pos ha)).2
  have hmoment' : (∫ ω, D n ω ^ 2 ∂P) ≤
      b ^ 2 * P.real (largeJumpCoverageEvent X b T K) +
        (2 * N) ^ 2 * P.real (largeJumpCoverageEvent X b T K)ᶜ + ε := hmoment
  have hle := div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_left hmoment' (by norm_num : (0 : ℝ) ≤ 4))
    (sq_nonneg (a / 2))
  exact hsplit.trans (add_le_add (hmaxbound.trans hle) hsmall.le)

end ProbabilityTheory
