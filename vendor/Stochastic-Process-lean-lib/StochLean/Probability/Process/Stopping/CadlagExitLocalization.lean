/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.Stopping.FirstExit
public import StochLean.Probability.Process.Path.CadlagBounded
public import StochLean.Probability.Process.Path.JumpStopping
public import Mathlib.Probability.Process.LocalProperty

/-! # Capped open norm exits for cadlag localization

The stopping sequence is the existing open norm hit, capped by its increasing
integer threshold. Cadlag compact bounds imply divergence. Strictly before
the exit, the path is bounded by the threshold, and the same bound holds for
its left limit at the exit. A bound on positive-time jumps controls overshoot.

Without a jump bound the stopped process is not claimed to be bounded. Only
its jumps away from the stopping endpoint are at most twice the threshold;
the non-strict inequality and the exceptional endpoint are retained.
-/

@[expose] public section

open MeasureTheory Filter Set
open scoped NNReal Topology

namespace ProbabilityTheory

variable {Ω : Type*} {X : ℝ≥0 → Ω → ℝ} {ω : Ω}

/-- The native open norm exit, capped at the same positive integer level. -/
noncomputable def cappedNormExitSequence (X : ℝ≥0 → Ω → ℝ) (n : ℕ)
    (ω : Ω) : WithTop ℝ≥0 :=
  min (hittingAfter X {x : ℝ | ((n + 1 : ℕ) : ℝ) < ‖x‖} 0 ω)
    (((n + 1 : ℕ) : ℝ≥0) : WithTop ℝ≥0)

theorem cappedNormExitSequence_le_hittingAfter (X : ℝ≥0 → Ω → ℝ) (n : ℕ) (ω : Ω) :
    cappedNormExitSequence X n ω ≤ hittingAfter X {x | ((n + 1 : ℕ) : ℝ) < ‖x‖} 0 ω :=
  min_le_left _ _

theorem cappedNormExitSequence_le (X : ℝ≥0 → Ω → ℝ) (n : ℕ) (ω : Ω) :
    cappedNormExitSequence X n ω ≤ (((n + 1 : ℕ) : ℝ≥0) : WithTop ℝ≥0) :=
  min_le_right _ _

theorem cappedNormExitSequence_ne_top (X : ℝ≥0 → Ω → ℝ) (n : ℕ) (ω : Ω) :
    cappedNormExitSequence X n ω ≠ ⊤ :=
  ne_top_of_le_ne_top WithTop.coe_ne_top (cappedNormExitSequence_le X n ω)

theorem monotone_cappedNormExitSequence (X : ℝ≥0 → Ω → ℝ) :
    Monotone (cappedNormExitSequence X) := by
  intro n m hnm ω
  apply min_le_min
  · apply hittingAfter_anti X 0 _ ω
    intro x hx
    exact (show ((n + 1 : ℕ) : ℝ) ≤ ((m + 1 : ℕ) : ℝ) from
      Nat.cast_le.mpr (Nat.add_le_add_right hnm 1)).trans_lt hx
  · exact WithTop.coe_le_coe.mpr (Nat.cast_le.mpr (Nat.add_le_add_right hnm 1))

theorem IsCadlagPath.tendsto_cappedNormExitSequence
    (hX : IsCadlagPath (X · ω)) :
    Tendsto (fun n ↦ cappedNormExitSequence X n ω) atTop (𝓝 ⊤) := by
  rw [WithTop.tendsto_nhds_top_iff]
  intro T
  obtain ⟨C, _, hC⟩ := hX.exists_norm_bound_Icc (T + 1)
  obtain ⟨N, hN⟩ := exists_nat_gt (max C (T : ℝ))
  filter_upwards [eventually_ge_atTop N] with n hn
  have hCn : C < ((n + 1 : ℕ) : ℝ) :=
    ((le_max_left _ _).trans_lt hN).trans_le
      (Nat.cast_le.mpr (hn.trans (Nat.le_succ n)))
  have hTn : (T : ℝ) < ((n + 1 : ℕ) : ℝ) :=
    ((le_max_right _ _).trans_lt hN).trans_le
      (Nat.cast_le.mpr (hn.trans (Nat.le_succ n)))
  apply lt_min
  · have hhit : ((T + 1 : ℝ≥0) : WithTop ℝ≥0) ≤
        hittingAfter X {x | ((n + 1 : ℕ) : ℝ) < ‖x‖} 0 ω := by
      by_contra h
      obtain ⟨t, ht, hval⟩ := hittingAfter_lt_iff.mp (lt_of_not_ge h)
      exact (not_lt_of_ge (hC t ⟨ht.1, ht.2.le⟩)) (hCn.trans hval)
    exact (WithTop.coe_lt_coe.mpr (lt_add_one T)).trans_le hhit
  · apply WithTop.coe_lt_coe.mpr
    exact_mod_cast hTn

theorem norm_le_of_lt_cappedNormExitSequence {n : ℕ} {t : ℝ≥0}
    (ht : (t : WithTop ℝ≥0) < cappedNormExitSequence X n ω) :
    ‖X t ω‖ ≤ ((n + 1 : ℕ) : ℝ) :=
  norm_le_of_lt_hittingAfter_norm
    (ht.trans_le (cappedNormExitSequence_le_hittingAfter X n ω))

/-- Left-limit control includes the possibly overshooting exit endpoint. -/
theorem IsCadlagPath.norm_leftLimitProcess_le_of_le_cappedNormExitSequence
    (hX : IsCadlagPath (X · ω)) {n : ℕ} {t : ℝ≥0}
    (ht : (t : WithTop ℝ≥0) ≤ cappedNormExitSequence X n ω) :
    ‖leftLimitProcess X t ω‖ ≤ ((n + 1 : ℕ) : ℝ) := by
  by_cases hz : t = 0
  · subst t
    simp only [leftLimitProcess_zero, Pi.zero_apply, norm_zero]
    positivity
  let : (𝓝[<] t).NeBot := nhdsLT_neBot_of_exists_lt ⟨0, pos_iff_ne_zero.mpr hz⟩
  apply le_of_tendsto (hX.tendsto_leftLimitProcess hz).norm
  filter_upwards [self_mem_nhdsWithin] with s hs
  exact norm_le_of_lt_cappedNormExitSequence ((WithTop.coe_lt_coe.mpr hs).trans_le ht)

/-- A zero-starting cadlag path has strictly positive cutoffs at every level. -/
theorem IsCadlagPath.cappedNormExitSequence_pos_of_zero
    (hX : IsCadlagPath (X · ω)) (h0 : X 0 ω = 0) (n : ℕ) :
    0 < cappedNormExitSequence X n ω := by
  apply lt_min
  · by_contra h
    have he : hittingAfter X {x | ((n + 1 : ℕ) : ℝ) < ‖x‖} 0 ω = 0 :=
      le_antisymm (le_of_not_gt h) bot_le
    have hne : hittingAfter X {x | ((n + 1 : ℕ) : ℝ) < ‖x‖} 0 ω ≠ ⊤ := by
      rw [he]
      exact WithTop.coe_ne_top
    have hl := le_norm_hittingAfter_norm_of_ne_top hX.1 hne
    rw [he] at hl
    change ((n + 1 : ℕ) : ℝ) ≤ ‖X 0 ω‖ at hl
    rw [h0, norm_zero] at hl
    exact (not_le_of_gt (by positivity : (0 : ℝ) < ((n + 1 : ℕ) : ℝ))) hl
  · exact WithTop.coe_lt_coe.mpr (by positivity)

/-- The jump hypothesis, not the open-exit definition, controls overshoot. -/
theorem IsCadlagPath.norm_le_of_le_cappedNormExitSequence_of_jump_bound
    (hX : IsCadlagPath (X · ω)) (h0 : X 0 ω = 0) {c : ℝ} (hc : 0 ≤ c)
    (hj : ∀ s : ℝ≥0, 0 < s → ‖jumpProcess X s ω‖ ≤ c) {n : ℕ} {t : ℝ≥0}
    (ht : (t : WithTop ℝ≥0) ≤ cappedNormExitSequence X n ω) :
    ‖X t ω‖ ≤ ((n + 1 : ℕ) : ℝ) + c := by
  by_cases hz : t = 0
  · subst t
    rw [h0, norm_zero]
    positivity
  have hl := hX.norm_leftLimitProcess_le_of_le_cappedNormExitSequence ht
  have h := norm_add_le (jumpProcess X t ω) (leftLimitProcess X t ω)
  have he : jumpProcess X t ω + leftLimitProcess X t ω = X t ω := sub_add_cancel _ _
  rw [he] at h
  exact h.trans ((add_le_add (hj t (pos_iff_ne_zero.mpr hz)) hl).trans_eq (add_comm _ _))

theorem IsCadlagPath.norm_stoppedProcess_cappedNormExitSequence_le_of_jump_bound
    (hX : IsCadlagPath (X · ω)) (h0 : X 0 ω = 0) {c : ℝ} (hc : 0 ≤ c)
    (hj : ∀ s : ℝ≥0, 0 < s → ‖jumpProcess X s ω‖ ≤ c) (n : ℕ) (t : ℝ≥0) :
    ‖stoppedProcess X (cappedNormExitSequence X n) t ω‖ ≤ ((n + 1 : ℕ) : ℝ) + c := by
  apply hX.norm_le_of_le_cappedNormExitSequence_of_jump_bound h0 hc hj
  have hne : min (t : WithTop ℝ≥0) (cappedNormExitSequence X n ω) ≠ ⊤ :=
    ne_top_of_le_ne_top WithTop.coe_ne_top (min_le_left _ _)
  rw [WithTop.untopA_eq_untop hne, WithTop.coe_untop]
  exact min_le_right _ _

/-- Without bounded jumps, only the stopping endpoint can carry a stopped
jump strictly larger than twice the level. Equality is not excluded. -/
theorem IsCadlagPath.norm_jumpProcess_stopped_cappedNormExitSequence_le_of_ne
    (hX : IsCadlagPath (X · ω)) {n : ℕ} {t : ℝ≥0}
    (hne : (t : WithTop ℝ≥0) ≠ cappedNormExitSequence X n ω) :
    ‖jumpProcess (stoppedProcess X (cappedNormExitSequence X n)) t ω‖ ≤
      2 * ((n + 1 : ℕ) : ℝ) := by
  rw [hX.jumpProcess_stoppedProcess]
  split_ifs with ht
  · have hstrict : (t : WithTop ℝ≥0) < cappedNormExitSequence X n ω :=
      lt_of_le_of_ne ht hne
    have hv := norm_le_of_lt_cappedNormExitSequence hstrict
    have hl := hX.norm_leftLimitProcess_le_of_le_cappedNormExitSequence ht
    change ‖X t ω - leftLimitProcess X t ω‖ ≤ _
    calc
      _ ≤ ‖X t ω‖ + ‖leftLimitProcess X t ω‖ := norm_sub_le _ _
      _ ≤ ((n + 1 : ℕ) : ℝ) + ((n + 1 : ℕ) : ℝ) := add_le_add hv hl
      _ = _ := (two_mul _).symm
  · rw [norm_zero]
    positivity

/-- The strict threshold identifies the exceptional endpoint; equality at
twice the level does not suffice for this conclusion. -/
theorem IsCadlagPath.eq_cappedNormExitSequence_of_lt_norm_jump_stopped
    (hX : IsCadlagPath (X · ω)) {n : ℕ} {t : ℝ≥0}
    (hj : 2 * ((n + 1 : ℕ) : ℝ) <
      ‖jumpProcess (stoppedProcess X (cappedNormExitSequence X n)) t ω‖) :
    (t : WithTop ℝ≥0) = cappedNormExitSequence X n ω := by
  by_contra hne
  exact (not_lt_of_ge
    (hX.norm_jumpProcess_stopped_cappedNormExitSequence_le_of_ne hne)) hj

variable {mΩ : MeasurableSpace Ω} {F : Filtration ℝ≥0 mΩ} {P : Measure Ω}

theorem HasCadlagPaths.ae_tendsto_cappedNormExitSequence (hX : HasCadlagPaths X P) :
    ∀ᵐ ω ∂P, Tendsto (fun n ↦ cappedNormExitSequence X n ω) atTop (𝓝 ⊤) :=
  hX.mono fun _ hω ↦ hω.tendsto_cappedNormExitSequence

theorem HasCadlagPaths.ae_cappedNormExitSequence_pos (hX : HasCadlagPaths X P)
    (h0 : X 0 =ᵐ[P] 0) : ∀ᵐ ω ∂P, ∀ n, 0 < cappedNormExitSequence X n ω := by
  filter_upwards [hX, h0] with ω hω h0ω n
  exact hω.cappedNormExitSequence_pos_of_zero h0ω n

theorem HasCadlagPaths.ae_norm_stoppedProcess_cappedNormExitSequence_le_of_jump_bound
    (hX : HasCadlagPaths X P) (h0 : X 0 =ᵐ[P] 0) {c : ℝ} (hc : 0 ≤ c)
    (hj : ∀ᵐ ω ∂P, ∀ t : ℝ≥0, 0 < t → ‖jumpProcess X t ω‖ ≤ c) :
    ∀ᵐ ω ∂P, ∀ (n : ℕ) (t : ℝ≥0),
      ‖stoppedProcess X (cappedNormExitSequence X n) t ω‖ ≤ ((n + 1 : ℕ) : ℝ) + c := by
  filter_upwards [hX, h0, hj] with ω hω h0ω hjω n t
  exact hω.norm_stoppedProcess_cappedNormExitSequence_le_of_jump_bound h0ω hc hjω n t

theorem HasCadlagPaths.ae_norm_jumpProcess_stopped_cappedNormExitSequence_le_of_ne
    (hX : HasCadlagPaths X P) : ∀ᵐ ω ∂P, ∀ (n : ℕ) (t : ℝ≥0),
      (t : WithTop ℝ≥0) ≠ cappedNormExitSequence X n ω →
      ‖jumpProcess (stoppedProcess X (cappedNormExitSequence X n)) t ω‖ ≤
        2 * ((n + 1 : ℕ) : ℝ) := by
  filter_upwards [hX] with ω hω n t hne
  exact hω.norm_jumpProcess_stopped_cappedNormExitSequence_le_of_ne hne

theorem HasCadlagPaths.ae_eq_cappedNormExitSequence_of_lt_norm_jump_stopped
    (hX : HasCadlagPaths X P) : ∀ᵐ ω ∂P, ∀ (n : ℕ) (t : ℝ≥0),
      2 * ((n + 1 : ℕ) : ℝ) <
          ‖jumpProcess (stoppedProcess X (cappedNormExitSequence X n)) t ω‖ →
        (t : WithTop ℝ≥0) = cappedNormExitSequence X n ω := by
  filter_upwards [hX] with ω hω n t hj
  exact hω.eq_cappedNormExitSequence_of_lt_norm_jump_stopped hj

end ProbabilityTheory

namespace MeasureTheory

open ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {F : Filtration ℝ≥0 mΩ}
  {P : Measure Ω} {X : ℝ≥0 → Ω → ℝ}

theorem Adapted.isStoppingTime_cappedNormExitSequence
    (ha : Adapted F X) (hF : F.IsUsual P) (hc : HasCadlagPaths X P) (n : ℕ) :
    IsStoppingTime F (cappedNormExitSequence X n) :=
  (ha.isStoppingTime_hittingAfter_norm_of_usual hF hc.hasRightContinuousPaths
    ((n + 1 : ℕ) : ℝ)).min (isStoppingTime_const F ((n + 1 : ℕ) : ℝ≥0))

theorem Adapted.isLocalizingSequence_cappedNormExitSequence
    (ha : Adapted F X) (hF : F.IsUsual P) (hc : HasCadlagPaths X P) :
    IsLocalizingSequence F (cappedNormExitSequence X) P :=
  ⟨⟨fun n ↦ ha.isStoppingTime_cappedNormExitSequence hF hc n,
    hc.ae_tendsto_cappedNormExitSequence⟩,
    Eventually.of_forall fun ω _n _m hnm ↦ monotone_cappedNormExitSequence X hnm ω⟩

end MeasureTheory
