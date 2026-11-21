/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Martingale.Doob.ConditionalModulusVersions
public import StochLean.Probability.Martingale.Doob.GlobalConditionalModulusStopping
public import StochLean.Probability.Martingale.Doob.LifetimeTailEnvelope

/-! # Global L2 conditional modulus for a randomly terminated process

Protter III.10, Lemma 3, with a version-safe essential supremum. A bounded adapted
cadlag process with totally inaccessible positive-time jumps, constant after an almost
surely finite stopping time, has global conditional increment modulus tending to zero
in probability and in L2. The supermartingale property and zero initial value are not
needed for this strengthened intermediate statement.

The proof first removes the random-lifetime tail by actual conditional martingale
envelopes, then uses the compact modulus theorem. Almost-sure finiteness is not
replaced by deterministic boundedness. No moment of the number of jumps is assumed.
-/

@[expose] public section

open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsFiniteMeasure P]
  {F : Filtration ℝ≥0 mΩ} {X : ℝ≥0 → Ω → ℝ} {N : ℝ} {τ : Ω → WithTop ℝ≥0}

theorem HasTotallyInaccessibleJumps.tendsto_measureReal_globalConditionalModulus_gt
    (hJ : HasTotallyInaccessibleJumps F X P) (hF : F.IsUsual P) (hX : Adapted F X)
    (hc : HasCadlagPaths X P) (hN : 0 ≤ N) (hbound : ∀ᵐ ω ∂P, ∀ t, ‖X t ω‖ ≤ N)
    (hτ : IsStoppingTime F τ) (hfinite : ∀ᵐ ω ∂P, τ ω ≠ ⊤)
    (hstop : ∀ᵐ ω ∂P, ∀ t u : ℝ≥0,
      τ ω ≤ (t : WithTop ℝ≥0) → t ≤ u → X t ω = X u ω)
    {G : ℝ≥0 → Ω → ℝ≥0∞} (hG : ∀ δ, IsGlobalConditionalIncrementModulus F P X δ (G δ))
    {a : ℝ} (ha : 0 < a) :
    Tendsto (fun δ ↦ P.real {ω | a < (G δ ω).toReal}) (𝓝 0) (𝓝 0) := by
  classical
  have hC : 0 ≤ 2 * N := mul_nonneg (by norm_num) hN
  obtain ⟨M, hM, hMlim⟩ := hτ.exists_cadlag_lifetimeTailEnvelopes_tendsto hF hfinite
  choose W hW using fun (n : ℕ) (δ : ℝ≥0) ↦ exists_conditionalIncrementModulus F P X n δ
  let q : ℝ := a / (2 * (2 * N + 1))
  have hq : 0 < q := by dsimp [q]; positivity
  have hsplit (n : ℕ) (δ : ℝ≥0) :
      P.real {ω | a < (G δ ω).toReal} ≤
        P.real {ω | a / 2 < (W n δ ω).toReal} +
          P.real {ω | q < (denseRunningSupremum (M n) n ω).toReal} := by
    have hdom := (hG δ).ae_bounds_of_stopping_time (hW n δ) hX hτ hstop hN hbound
      (M n) (hM n).2.1.hasRightContinuousPaths (hM n).2.2.1
    have hsum : (fun ω ↦ (G δ ω).toReal) ≤ᵐ[P]
        (fun ω ↦ (W n δ ω).toReal + 2 * N *
          ∑ _i ∈ ({0} : Finset ℕ), (denseRunningSupremum (M n) n ω).toReal) := by
      filter_upwards [hdom] with ω hω
      simpa only [Finset.sum_singleton] using hω.2.2.2.2
    simpa only [Finset.sum_singleton, Finset.card_singleton, Nat.cast_one, mul_one] using
      measureReal_gt_le_of_ae_le_add_finset_mul ({0} : Finset ℕ) hC ha hsum
  refine tendsto_order.mpr ⟨?_, ?_⟩
  · intro z hz
    exact Eventually.of_forall fun _ ↦ hz.trans_le measureReal_nonneg
  · intro z hz
    obtain ⟨n, hn⟩ := ((hMlim (fun n ↦ (n : ℝ≥0)) q hq).eventually_lt_const
      (half_pos hz)).exists
    have hcprob := (hJ.tendstoInMeasure_conditionalModulus_of_hasCadlagPaths hF hX hc
      hN hbound (hW n)).tendsto_measureReal_gt_zero (half_pos ha)
    filter_upwards [hcprob.eventually_lt_const (half_pos hz)] with δ hδ
    have hs := hsplit n δ
    linarith only [hs, hn, hδ]

theorem HasTotallyInaccessibleJumps.tendstoInMeasure_globalConditionalModulus
    (hJ : HasTotallyInaccessibleJumps F X P) (hF : F.IsUsual P) (hX : Adapted F X)
    (hc : HasCadlagPaths X P) (hN : 0 ≤ N) (hbound : ∀ᵐ ω ∂P, ∀ t, ‖X t ω‖ ≤ N)
    (hτ : IsStoppingTime F τ) (hfinite : ∀ᵐ ω ∂P, τ ω ≠ ⊤)
    (hstop : ∀ᵐ ω ∂P, ∀ t u : ℝ≥0,
      τ ω ≤ (t : WithTop ℝ≥0) → t ≤ u → X t ω = X u ω)
    {G : ℝ≥0 → Ω → ℝ≥0∞} (hG : ∀ δ, IsGlobalConditionalIncrementModulus F P X δ (G δ)) :
    TendstoInMeasure P (fun δ ω ↦ (G δ ω).toReal) (𝓝 0) (fun _ ↦ (0 : ℝ)) :=
  tendstoInMeasure_zero_of_nonneg_of_measureReal_gt
    (fun _ ↦ Eventually.of_forall fun _ ↦ ENNReal.toReal_nonneg)
    (fun _ ha ↦ hJ.tendsto_measureReal_globalConditionalModulus_gt hF hX hc hN hbound
      hτ hfinite hstop hG ha)

theorem HasTotallyInaccessibleJumps.globalConditionalModulus_L2_convergence
    (hJ : HasTotallyInaccessibleJumps F X P) (hF : F.IsUsual P) (hX : Adapted F X)
    (hc : HasCadlagPaths X P) (hN : 0 ≤ N) (hbound : ∀ᵐ ω ∂P, ∀ t, ‖X t ω‖ ≤ N)
    (hτ : IsStoppingTime F τ) (hfinite : ∀ᵐ ω ∂P, τ ω ≠ ⊤)
    (hstop : ∀ᵐ ω ∂P, ∀ t u : ℝ≥0,
      τ ω ≤ (t : WithTop ℝ≥0) → t ≤ u → X t ω = X u ω)
    {G : ℝ≥0 → Ω → ℝ≥0∞} (hG : ∀ δ, IsGlobalConditionalIncrementModulus F P X δ (G δ)) :
    (∀ δ, MemLp (fun ω ↦ (G δ ω).toReal) 2 P) ∧
      Tendsto (fun δ ↦ ∫ ω, (G δ ω).toReal ^ 2 ∂P) (𝓝 0) (𝓝 0) ∧
        Tendsto (fun δ ↦ eLpNorm (fun ω ↦ (G δ ω).toReal) 2 P) (𝓝 0) (𝓝 0) := by
  have hC : 0 ≤ 2 * N := mul_nonneg (by norm_num) hN
  have hi (t : ℝ≥0) : Integrable (X t) P :=
    (MemLp.of_bound ((hX t).mono (F.le t) le_rfl).aestronglyMeasurable N
      (hbound.mono fun _ hω ↦ hω t) (p := 1)).integrable le_rfl
  have hcap (δ : ℝ≥0) : ∀ᵐ ω ∂P, ‖(G δ ω).toReal‖ ≤ 2 * N := by
    filter_upwards [(hG δ).ae_le_of_norm_bound hi
      (fun t ↦ hbound.mono fun _ hω ↦ hω t)] with ω hω
    rw [Real.norm_of_nonneg ENNReal.toReal_nonneg]
    simpa only [ENNReal.toReal_ofReal hC] using
      ENNReal.toReal_mono ENNReal.ofReal_ne_top hω
  have hm (δ : ℝ≥0) : AEStronglyMeasurable (fun ω ↦ (G δ ω).toReal) P :=
    (hG δ).measurable.ennreal_toReal.aestronglyMeasurable
  have hlim := hJ.tendstoInMeasure_globalConditionalModulus hF hX hc hN hbound
    hτ hfinite hstop hG
  exact ⟨fun δ ↦ MemLp.of_bound (hm δ) (2 * N) (hcap δ),
    hlim.tendsto_integral_sq_of_bound hm hC hcap,
    hlim.tendsto_eLpNorm_two_of_bound hm hC hcap⟩

/-- The actual global moduli exist and have the asserted limits; no modulus or convergence
certificate is required as input. Each modulus retains its essential-supremum specification. -/
theorem HasTotallyInaccessibleJumps.exists_globalConditionalModulus_L2_convergence
    (hJ : HasTotallyInaccessibleJumps F X P) (hF : F.IsUsual P) (hX : Adapted F X)
    (hc : HasCadlagPaths X P) (hN : 0 ≤ N) (hbound : ∀ᵐ ω ∂P, ∀ t, ‖X t ω‖ ≤ N)
    (hτ : IsStoppingTime F τ) (hfinite : ∀ᵐ ω ∂P, τ ω ≠ ⊤)
    (hstop : ∀ᵐ ω ∂P, ∀ t u : ℝ≥0,
      τ ω ≤ (t : WithTop ℝ≥0) → t ≤ u → X t ω = X u ω) :
    ∃ G : ℝ≥0 → Ω → ℝ≥0∞, (∀ δ, IsGlobalConditionalIncrementModulus F P X δ (G δ)) ∧
      TendstoInMeasure P (fun δ ω ↦ (G δ ω).toReal) (𝓝 0) (fun _ ↦ (0 : ℝ)) ∧
        (∀ δ, MemLp (fun ω ↦ (G δ ω).toReal) 2 P) ∧
          Tendsto (fun δ ↦ ∫ ω, (G δ ω).toReal ^ 2 ∂P) (𝓝 0) (𝓝 0) ∧
            Tendsto (fun δ ↦ eLpNorm (fun ω ↦ (G δ ω).toReal) 2 P) (𝓝 0) (𝓝 0) := by
  choose G hG using fun δ ↦ exists_globalConditionalIncrementModulus F P X δ
  exact ⟨G, hG,
    hJ.tendstoInMeasure_globalConditionalModulus hF hX hc hN hbound hτ hfinite hstop hG,
    hJ.globalConditionalModulus_L2_convergence hF hX hc hN hbound hτ hfinite hstop hG⟩

end ProbabilityTheory
