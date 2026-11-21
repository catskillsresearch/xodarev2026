/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Martingale.Doob.SingleJumpTruncation
public import StochLean.Probability.Martingale.Doob.ContinuousComparison
public import StochLean.Probability.Process.UCP.MonotoneTail

/-! # Comparing continuous compensators of clipped single jumps

The given compensators are the actual outputs of the bounded single-jump
existence theorem. A larger clipping level minus a smaller one is an actual
bounded negative-jump supermartingale. Continuous compensator comparison
therefore makes the compensator difference increasing. Its mean is bounded
by the integrable amplitude tail, which proves UCP-Cauchy convergence without
introducing a terminal compensator or assuming any convergence conclusion.
-/

@[expose] public section

open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
  {F : Filtration ℝ≥0 mΩ} {τ : Ω → WithTop ℝ≥0} {C : Ω → ℝ}
  {A : ℕ → ℝ≥0 → Ω → ℝ}

local notation "J" => (fun (n : ℕ) (t : ℝ≥0) ↦
  Set.indicator (Set.ofPred (fun ω ↦ τ ω ≤ (t : WithTop ℝ≥0)))
    (fun ω ↦ -min (C ω) (n : ℝ)))

private theorem clipped_jump_difference_data
    (hτ : IsTotallyInaccessibleStoppingTime F τ P)
    (hm : StronglyMeasurable[hτ.1.measurableSpace] C) (hi : Integrable C P)
    (hn : ∀ᵐ ω ∂P, 0 ≤ C ω) {n m : ℕ} (hnm : n ≤ m) :
    Supermartingale (J m - J n) F P ∧ HasCadlagPaths (J m - J n) P ∧
      HasTotallyInaccessibleJumps F (J m - J n) P ∧
      ∀ᵐ ω ∂P, ∀ t, ‖(J m - J n) t ω‖ ≤ (m : ℝ) := by
  have he : J m - J n = (fun t : ℝ≥0 ↦
      {ω | τ ω ≤ (t : WithTop ℝ≥0)}.indicator
        (fun ω ↦ -min (C ω) (m : ℝ) - -min (C ω) (n : ℝ))) := by
    funext t ω
    simp only [Pi.sub_apply, indicator_sub]
  rw [he]
  refine ⟨supermartingale_indicator_stoppingTime_le_neg_min_sub hτ.1 hm hi
    (Nat.cast_le.mpr hnm), ?_, hτ.hasTotallyInaccessibleJumps_indicator _, ?_⟩
  · exact Eventually.of_forall (isCadlagPath_indicator_lifetime_le τ _)
  · filter_upwards [hn] with ω hω t
    apply (norm_indicator_le_norm_self _ _).trans
    have hord : min (C ω) (n : ℝ) ≤ min (C ω) (m : ℝ) :=
      min_le_min le_rfl (Nat.cast_le.mpr hnm)
    rw [Real.norm_of_nonpos (show -min (C ω) (m : ℝ) - -min (C ω) (n : ℝ) ≤ 0 by
      linarith)]
    have hlow : 0 ≤ min (C ω) (n : ℝ) := le_min hω (Nat.cast_nonneg _)
    linarith [min_le_right (C ω) (m : ℝ)]

/-- Coordinate integrability is derived from the true martingale minus the
integrable clipped jump; it is not inferred from the martingale sum alone. -/
theorem IsTotallyInaccessibleStoppingTime.integrable_continuous_compensator_neg_min
    (hτ : IsTotallyInaccessibleStoppingTime F τ P)
    (hm : StronglyMeasurable[hτ.1.measurableSpace] C) (hi : Integrable C P)
    (hn : ∀ᵐ ω ∂P, 0 ≤ C ω)
    (hMA : ∀ n, Martingale (J n + A n) F P) (n : ℕ) (t : ℝ≥0) :
    Integrable (A n t) P := by
  have hX := supermartingale_indicator_stoppingTime_le_neg_min hτ.1 hm hi hn
    (Nat.cast_nonneg n : (0 : ℝ) ≤ n)
  have he : A n t = (J n + A n) t - J n t := by
    funext ω
    simp only [Pi.sub_apply, Pi.add_apply]
    ring
  rw [he]
  exact ((hMA n).integrable t).sub (hX.integrable t)

/-- Ordered clipping levels have an increasing compensator difference. This
uses the supermartingale property of the actual clipping difference. -/
theorem IsTotallyInaccessibleStoppingTime.hasMonotonePaths_sub_continuous_compensators_neg_min
    (hτ : IsTotallyInaccessibleStoppingTime F τ P) (hF : F.IsUsual P)
    (hm : StronglyMeasurable[hτ.1.measurableSpace] C) (hi : Integrable C P)
    (hn : ∀ᵐ ω ∂P, 0 ≤ C ω)
    (hcA : ∀ n, HasContinuousPaths (A n) P)
    (hvA : ∀ n, HasFiniteVariationPaths (A n) P)
    (hA0 : ∀ n, A n 0 =ᵐ[P] 0) (hMA : ∀ n, Martingale (J n + A n) F P)
    {n m : ℕ} (hnm : n ≤ m) : HasMonotonePaths (A m - A n) P := by
  obtain ⟨hD, hcD, hJD, hbD⟩ := clipped_jump_difference_data hτ hm hi hn hnm
  exact hD.hasMonotonePaths_sub_continuous_compensators hF hcD hJD (Nat.cast_nonneg m)
    hbD (hMA n) (hMA m) (hcA n) (hcA m) (hvA n) (hvA m) (hA0 n) (hA0 m)

/-- Compensator order holds at all times on one common full-measure event. -/
theorem IsTotallyInaccessibleStoppingTime.ae_forall_le_continuous_compensators_neg_min
    (hτ : IsTotallyInaccessibleStoppingTime F τ P) (hF : F.IsUsual P)
    (hm : StronglyMeasurable[hτ.1.measurableSpace] C) (hi : Integrable C P)
    (hn : ∀ᵐ ω ∂P, 0 ≤ C ω)
    (hcA : ∀ n, HasContinuousPaths (A n) P)
    (hvA : ∀ n, HasFiniteVariationPaths (A n) P)
    (hA0 : ∀ n, A n 0 =ᵐ[P] 0) (hMA : ∀ n, Martingale (J n + A n) F P)
    {n m : ℕ} (hnm : n ≤ m) : ∀ᵐ ω ∂P, ∀ t, A n t ω ≤ A m t ω := by
  have hmono := hτ.hasMonotonePaths_sub_continuous_compensators_neg_min
    hF hm hi hn hcA hvA hA0 hMA hnm
  filter_upwards [hmono, hA0 n, hA0 m] with ω hω hnω hmω t
  have h := hω (show (0 : ℝ≥0) ≤ t from bot_le)
  change A m 0 ω - A n 0 ω ≤ A m t ω - A n t ω at h
  rw [hnω, hmω] at h
  linarith

/-- The mean compensator difference is at most the actual remaining
amplitude. Integrability of all compensator coordinates is proved internally. -/
theorem IsTotallyInaccessibleStoppingTime.integral_sub_continuous_compensators_neg_min_le
    (hτ : IsTotallyInaccessibleStoppingTime F τ P)
    (hm : StronglyMeasurable[hτ.1.measurableSpace] C) (hi : Integrable C P)
    (hn : ∀ᵐ ω ∂P, 0 ≤ C ω)
    (hA0 : ∀ n, A n 0 =ᵐ[P] 0) (hMA : ∀ n, Martingale (J n + A n) F P)
    (n m : ℕ) (t : ℝ≥0) :
    (∫ ω, (A m - A n) t ω ∂P) ≤ ∫ ω, C ω - min (C ω) (n : ℝ) ∂P := by
  have hiX (k : ℕ) : Integrable (J k t) P :=
    (supermartingale_indicator_stoppingTime_le_neg_min hτ.1 hm hi hn
      (Nat.cast_nonneg k)).integrable t
  have hiA (k : ℕ) : Integrable (A k t) P :=
    hτ.integrable_continuous_compensator_neg_min hm hi hn hMA k t
  have he : (J m - J n) + (A m - A n) = (J m + A m) - (J n + A n) := by
    funext s ω
    simp only [Pi.sub_apply, Pi.add_apply]
    ring
  have hMD : Martingale ((J m - J n) + (A m - A n)) F P := by
    rw [he]
    exact (hMA m).sub (hMA n)
  have hD0 : (J m - J n) 0 =ᵐ[P] 0 := by
    filter_upwards [hτ.indicator_initial_ae_eq_zero (fun ω ↦ -min (C ω) (m : ℝ)),
      hτ.indicator_initial_ae_eq_zero (fun ω ↦ -min (C ω) (n : ℝ))] with ω hmω hnω
    change J m 0 ω - J n 0 ω = 0
    exact sub_eq_zero.mpr (hmω.trans hnω.symm)
  have hAD0 : (A m - A n) 0 =ᵐ[P] 0 := by
    filter_upwards [hA0 m, hA0 n] with ω hmω hnω
    change A m 0 ω - A n 0 ω = 0
    rw [hmω, hnω]
    exact sub_self _
  have hmean := hMD.integral_add_compensator_eq hAD0 t
    ((hiX m).sub (hiX n)) ((hiA m).sub (hiA n))
  rw [integral_congr_ae hD0] at hmean
  simp only [Pi.zero_apply, integral_zero, zero_sub] at hmean
  rw [hmean, ← integral_neg]
  apply integral_mono_ae ((hiX m).sub (hiX n)).neg (hi.sub (hi.inf (integrable_const _)))
  apply Eventually.of_forall
  intro ω
  change -(J m t ω - J n t ω) ≤ C ω - min (C ω) (n : ℝ)
  by_cases ht : τ ω ≤ (t : WithTop ℝ≥0)
  · simp only [indicator_apply, mem_ofPred_eq, if_pos ht]
    linarith [min_le_left (C ω) (m : ℝ)]
  · simp only [indicator_apply, mem_ofPred_eq, if_neg ht, sub_self, neg_zero]
    exact sub_nonneg.mpr (min_le_left _ _)

/-- The actual bounded clipped-jump compensators are UCP-Cauchy, with no
terminal compensator or convergence hypothesis in the premises. -/
theorem IsTotallyInaccessibleStoppingTime.cauchyUCP_continuous_compensators_neg_min
    (hτ : IsTotallyInaccessibleStoppingTime F τ P) (hF : F.IsUsual P)
    (hm : StronglyMeasurable[hτ.1.measurableSpace] C) (hi : Integrable C P)
    (hn : ∀ᵐ ω ∂P, 0 ≤ C ω)
    (hcA : ∀ n, HasContinuousPaths (A n) P)
    (hvA : ∀ n, HasFiniteVariationPaths (A n) P)
    (hA0 : ∀ n, A n 0 =ᵐ[P] 0) (hMA : ∀ n, Martingale (J n + A n) F P) :
    CauchyUCP P A := by
  apply cauchyUCP_of_monotone_sub_integral_tail
    (e := fun n ↦ ∫ ω, C ω - min (C ω) (n : ℝ) ∂P)
    (fun n m hnm ↦ hτ.hasMonotonePaths_sub_continuous_compensators_neg_min
      hF hm hi hn hcA hvA hA0 hMA hnm) hA0
    (hτ.integrable_continuous_compensator_neg_min hm hi hn hMA)
    (hi.tendsto_integral_sub_min_nat hn)
  exact fun n m _ t ↦ hτ.integral_sub_continuous_compensators_neg_min_le hm hi hn hA0 hMA n m t

end ProbabilityTheory
