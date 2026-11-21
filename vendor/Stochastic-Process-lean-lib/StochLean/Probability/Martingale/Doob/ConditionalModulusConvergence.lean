/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Martingale.Doob.ConditionalModulusTail
public import StochLean.ForMathlib.MeasureTheory.Function.BoundedMomentConvergence

/-! # Compact conditional increment moduli tend to zero

Actual finite large-jump residual estimates imply convergence in probability, first for
positive width sequences and then for every width tending to zero. The fixed original
process bound upgrades this to second-moment and native L2-seminorm convergence.

These compact-horizon statements need no supermartingale property or initial normalization.
They do not by themselves identify a full half-line modulus for a process stopped at a
random finite lifetime.
-/

@[expose] public section

open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsFiniteMeasure P]
  {F : Filtration ℝ≥0 mΩ} {X : ℝ≥0 → Ω → ℝ} {N : ℝ} {T : ℝ≥0}

theorem HasTotallyInaccessibleJumps.tendsto_measureReal_conditionalModulus_gt_seq
    (hJ : HasTotallyInaccessibleJumps F X P) (hF : F.IsUsual P) (hX : Adapted F X)
    (hc : ∀ ω, IsCadlagPath (X · ω)) (hN : 0 ≤ N)
    (hbound : ∀ᵐ ω ∂P, ∀ t, ‖X t ω‖ ≤ N)
    {δ : ℕ → ℝ≥0} (hδ : Tendsto δ atTop (𝓝 0)) (hδpos : ∀ n, 0 < δ n)
    {W : ℕ → Ω → ℝ≥0∞} (hW : ∀ n, IsConditionalIncrementModulus F P X T (δ n) (W n))
    {a : ℝ} (ha : 0 < a) :
    Tendsto (fun n ↦ P.real {ω | a < (W n ω).toReal}) atTop (𝓝 0) := by
  let : F.IsRightContinuous := hF.rightContinuous
  let d : ℕ → ℝ := fun n ↦ 1 / ((n : ℝ) + 1)
  have hd : Tendsto d atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have hdpos (n : ℕ) : 0 < d n := by dsimp [d]; positivity
  refine tendsto_order.mpr ⟨?_, ?_⟩
  · intro z hz
    exact Eventually.of_forall fun _ ↦ hz.trans_le measureReal_nonneg
  · intro z hz
    have hbLim : Tendsto (fun j ↦ 4 * (d j ^ 2 * P.real univ) / (a / 2) ^ 2)
        atTop (𝓝 0) := by
      simpa only [zero_pow (by decide : 2 ≠ 0), zero_mul, mul_zero, zero_div] using
        (((hd.pow 2).mul_const (P.real univ)).const_mul 4).div_const ((a / 2) ^ 2)
    obtain ⟨j, hj⟩ := (hbLim.eventually_lt_const hz).exists
    have hb := hdpos j
    have hbad := hX.tendsto_measureReal_largeJumpCoverageEvent_compl (P := P) hc hb T
    have hKLim : Tendsto (fun K ↦
        4 * (d j ^ 2 * P.real univ +
          (2 * N) ^ 2 * P.real (largeJumpCoverageEvent X (d j) T K)ᶜ) / (a / 2) ^ 2)
        atTop (𝓝 (4 * (d j ^ 2 * P.real univ) / (a / 2) ^ 2)) := by
      simpa only [mul_zero, add_zero] using
        ((hbad.const_mul ((2 * N) ^ 2)).const_add (d j ^ 2 * P.real univ)).const_mul 4
          |>.div_const ((a / 2) ^ 2)
    obtain ⟨K, hK⟩ := (hKLim.eventually_lt_const hj).exists
    have heLim : Tendsto (fun k ↦
        4 * (d j ^ 2 * P.real univ +
          (2 * N) ^ 2 * P.real (largeJumpCoverageEvent X (d j) T K)ᶜ + d k) /
            (a / 2) ^ 2 + d k) atTop
        (𝓝 (4 * (d j ^ 2 * P.real univ +
          (2 * N) ^ 2 * P.real (largeJumpCoverageEvent X (d j) T K)ᶜ) / (a / 2) ^ 2)) := by
      simpa only [add_zero] using
        (((hd.const_add (d j ^ 2 * P.real univ +
          (2 * N) ^ 2 * P.real (largeJumpCoverageEvent X (d j) T K)ᶜ)).const_mul 4).div_const
            ((a / 2) ^ 2)).add hd
    obtain ⟨k, hk⟩ := (heLim.eventually_lt_const hK).exists
    have htail := hJ.eventually_measureReal_conditionalModulus_gt_le hF hX hc hN hbound
      hb K hδ hδpos hW ha (hdpos k)
    filter_upwards [htail] with n hn
    apply hn.trans_lt
    apply lt_of_le_of_lt _ hk
    have hmeasure : P.real (largeJumpCoverageEvent X (d j) T K) ≤ P.real univ :=
      measureReal_mono (subset_univ _) (measure_ne_top _ _)
    gcongr

theorem HasTotallyInaccessibleJumps.tendsto_measureReal_conditionalModulus_gt
    (hJ : HasTotallyInaccessibleJumps F X P) (hF : F.IsUsual P) (hX : Adapted F X)
    (hc : ∀ ω, IsCadlagPath (X · ω)) (hN : 0 ≤ N)
    (hbound : ∀ᵐ ω ∂P, ∀ t, ‖X t ω‖ ≤ N)
    {W : ℝ≥0 → Ω → ℝ≥0∞} (hW : ∀ δ, IsConditionalIncrementModulus F P X T δ (W δ))
    {a : ℝ} (ha : 0 < a) :
    Tendsto (fun δ ↦ P.real {ω | a < (W δ ω).toReal}) (𝓝 0) (𝓝 0) := by
  have hi (t : ℝ≥0) : Integrable (X t) P :=
    (MemLp.of_bound ((hX t).mono (F.le t) le_rfl).aestronglyMeasurable N
      (hbound.mono fun _ hω ↦ hω t) (p := 1)).integrable le_rfl
  have hfin (δ : ℝ≥0) : ∀ᵐ ω ∂P, W δ ω ≠ ∞ :=
    (hW δ).ae_ne_top_of_norm_bound (fun t _ ↦ hi t)
      (fun t _ ↦ hbound.mono fun _ hω ↦ hω t)
  have hmono : Monotone (fun δ ↦ P.real {ω | a < (W δ ω).toReal}) := by
    intro δ η hδη
    apply ENNReal.toReal_mono (measure_ne_top _ _)
    apply measure_mono_ae
    filter_upwards [(hW δ).mono_width (hW η) hδη, hfin η] with ω hle hfinite hmem
    exact hmem.trans_le (ENNReal.toReal_mono hfinite hle)
  let d : ℕ → ℝ≥0 := fun n ↦ 1 / ((n : ℝ≥0) + 1)
  have hd : Tendsto d atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have hdpos (n : ℕ) : 0 < d n := by dsimp [d]; positivity
  have hseq := hJ.tendsto_measureReal_conditionalModulus_gt_seq hF hX hc hN hbound
    hd hdpos (fun n ↦ hW (d n)) ha
  refine tendsto_order.mpr ⟨?_, ?_⟩
  · intro z hz
    exact Eventually.of_forall fun _ ↦ hz.trans_le measureReal_nonneg
  · intro z hz
    obtain ⟨n, hn⟩ := (hseq.eventually_lt_const hz).exists
    filter_upwards [Iio_mem_nhds (hdpos n)] with δ hδ
    exact (hmono hδ.le).trans_lt hn

theorem HasTotallyInaccessibleJumps.tendstoInMeasure_conditionalModulus
    (hJ : HasTotallyInaccessibleJumps F X P) (hF : F.IsUsual P) (hX : Adapted F X)
    (hc : ∀ ω, IsCadlagPath (X · ω)) (hN : 0 ≤ N)
    (hbound : ∀ᵐ ω ∂P, ∀ t, ‖X t ω‖ ≤ N)
    {W : ℝ≥0 → Ω → ℝ≥0∞} (hW : ∀ δ, IsConditionalIncrementModulus F P X T δ (W δ)) :
    TendstoInMeasure P (fun δ ω ↦ (W δ ω).toReal) (𝓝 0) (fun _ ↦ (0 : ℝ)) :=
  tendstoInMeasure_zero_of_nonneg_of_measureReal_gt
    (fun _ ↦ Eventually.of_forall fun _ ↦ ENNReal.toReal_nonneg)
    (fun _ ha ↦ hJ.tendsto_measureReal_conditionalModulus_gt hF hX hc hN hbound hW ha)

theorem HasTotallyInaccessibleJumps.conditionalModulus_L2_convergence
    (hJ : HasTotallyInaccessibleJumps F X P) (hF : F.IsUsual P) (hX : Adapted F X)
    (hc : ∀ ω, IsCadlagPath (X · ω)) (hN : 0 ≤ N)
    (hbound : ∀ᵐ ω ∂P, ∀ t, ‖X t ω‖ ≤ N)
    {W : ℝ≥0 → Ω → ℝ≥0∞} (hW : ∀ δ, IsConditionalIncrementModulus F P X T δ (W δ)) :
    (∀ δ, MemLp (fun ω ↦ (W δ ω).toReal) 2 P) ∧
      Tendsto (fun δ ↦ ∫ ω, (W δ ω).toReal ^ 2 ∂P) (𝓝 0) (𝓝 0) ∧
        Tendsto (fun δ ↦ eLpNorm (fun ω ↦ (W δ ω).toReal) 2 P) (𝓝 0) (𝓝 0) := by
  have hC : 0 ≤ 2 * N := mul_nonneg (by norm_num) hN
  have hi (t : ℝ≥0) : Integrable (X t) P :=
    (MemLp.of_bound ((hX t).mono (F.le t) le_rfl).aestronglyMeasurable N
      (hbound.mono fun _ hω ↦ hω t) (p := 1)).integrable le_rfl
  have hcap (δ : ℝ≥0) : ∀ᵐ ω ∂P, ‖(W δ ω).toReal‖ ≤ 2 * N := by
    filter_upwards [(hW δ).ae_le_of_norm_bound (fun t _ ↦ hi t)
      (fun t _ ↦ hbound.mono fun _ hω ↦ hω t)] with ω hω
    rw [Real.norm_of_nonneg ENNReal.toReal_nonneg]
    simpa only [ENNReal.toReal_ofReal hC] using
      ENNReal.toReal_mono ENNReal.ofReal_ne_top hω
  have hm (δ : ℝ≥0) : AEStronglyMeasurable (fun ω ↦ (W δ ω).toReal) P :=
    (hW δ).measurable.ennreal_toReal.aestronglyMeasurable
  have hlim := hJ.tendstoInMeasure_conditionalModulus hF hX hc hN hbound hW
  exact ⟨fun δ ↦ MemLp.of_bound (hm δ) (2 * N) (hcap δ),
    hlim.tendsto_integral_sq_of_bound hm hC hcap,
    hlim.tendsto_eLpNorm_two_of_bound hm hC hcap⟩

end ProbabilityTheory
