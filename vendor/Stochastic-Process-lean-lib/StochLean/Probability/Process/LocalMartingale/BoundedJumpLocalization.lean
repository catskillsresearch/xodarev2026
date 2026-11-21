/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.Stopping.CadlagExitLocalization
public import StochLean.Probability.Process.LocalMartingale.Bounded
public import StochLean.Probability.Process.LocalMartingale.Reducing
public import StochLean.Probability.Process.LocalMartingale.InitialValue
public import StochLean.Probability.Process.Path.LeftLimitOperations

/-! # Actual square-integrable localization from bounded positive-time jumps

For zero initial value, the existing capped norm exits have bounded overshoot
because the positive-time jumps are bounded. Stopping preserves the original
local-martingale predicate; its actual uniform path bound then proves true UI
martingality and finite-time square integrability.

An arbitrary initial random value is handled by centering and intersecting
the centered capped exits with the existing initial-value localizer. On the
positive-lifetime mask, both the initial value and the stopped centered path
are bounded. This constructs an actual bounded fundamental sequence for the
original process and hence the native locally square-integrable property.

No integrability of the unmasked initial value, semimartingale witness,
continuous paths, or new local-martingale/localization definition is used.
The jump assumption excludes time zero, where the source jump equals the
original initial value and need not be bounded.
-/

@[expose] public section

open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsFiniteMeasure P]
  {F : Filtration ℝ≥0 mΩ} {X : ℝ≥0 → Ω → ℝ} {C : ℝ}

/-- The actual capped exits of a zero-starting bounded-jump local martingale
give true square-integrable stopped martingales, including the exit jump. -/
theorem IsLocalMartingale.squareIntegrable_stopped_cappedNormExitSequence_of_jump_bound
    (hX : IsLocalMartingale X F P) (hF : F.IsUsual P) (h0 : X 0 =ᵐ[P] 0)
    (hC : 0 ≤ C) (hj : ∀ᵐ ω ∂P, ∀ t : ℝ≥0, 0 < t → ‖jumpProcess X t ω‖ ≤ C)
    (n : ℕ) : IsSquareIntegrableMartingale
      (MeasureTheory.stoppedProcess X (cappedNormExitSequence X n)) F P := by
  let B : ℝ≥0 := ⟨((n + 1 : ℕ) : ℝ) + C, by positivity⟩
  have hb : ∀ᵐ ω ∂P, ∀ t,
      ‖MeasureTheory.stoppedProcess X (cappedNormExitSequence X n) t ω‖ ≤ (B : ℝ) :=
    (hX.2.1.ae_norm_stoppedProcess_cappedNormExitSequence_le_of_jump_bound h0 hC hj).mono
      (fun _ hω ↦ hω n)
  have hu := (hX.stoppedProcess hF
    (hX.1.isStoppingTime_cappedNormExitSequence hF hX.2.1 n)).isUIMartingale_of_bound B hb
  exact ⟨hu.1, fun t ↦ MemLp.of_bound (hu.1.integrable t).aestronglyMeasurable (B : ℝ)
    (hb.mono fun _ hω ↦ hω t)⟩

/-- Centered capped exits intersected with the native initial-value localizer
give an actual bounded fundamental sequence. Arbitrary finite initial values
are retained; only the positive-lifetime masked stopped processes are bounded. -/
theorem IsLocalMartingale.exists_bounded_fundamentalSequence_of_jump_bound
    (hX : IsLocalMartingale X F P) (hF : F.IsUsual P)
    (hC : 0 ≤ C) (hj : ∀ᵐ ω ∂P, ∀ t : ℝ≥0, 0 < t → ‖jumpProcess X t ω‖ ≤ C) :
    ∃ σ : ℕ → Ω → WithTop ℝ≥0, IsFundamentalSequence X F P σ ∧
      ∀ n, (∀ᵐ ω ∂P, ∀ t, ‖MeasureTheory.stoppedProcess
        (fun s ↦ {ω | 0 < σ n ω}.indicator (X s)) (σ n) t ω‖ ≤ 2 * (n : ℝ) + 1 + C) ∧
        IsSquareIntegrableMartingale (MeasureTheory.stoppedProcess
          (fun s ↦ {ω | 0 < σ n ω}.indicator (X s)) (σ n)) F P := by
  classical
  let Y : ℝ≥0 → Ω → ℝ := fun t ω ↦ X t ω - X 0 ω
  have hY : IsLocalMartingale Y F P :=
    hX.sub (isContinuousLocalMartingale_const_initial (hX.1 0)).1 hF
  have hY0 : Y 0 =ᵐ[P] 0 := Eventually.of_forall fun _ ↦ sub_self _
  have hjY : ∀ᵐ ω ∂P, ∀ t : ℝ≥0, 0 < t → ‖jumpProcess Y t ω‖ ≤ C := by
    filter_upwards [hX.2.1, hj] with ω hcω hjω t ht
    have hc0 : IsCadlagPath (fun _ : ℝ≥0 ↦ X 0 ω) :=
      IsContinuousPath.isCadlagPath continuous_const
    have hz : jumpProcess (fun _ : ℝ≥0 ↦ X 0) t ω = 0 :=
      IsContinuousPath.jumpProcess_eq_zero (X := fun _ : ℝ≥0 ↦ X 0) (ω := ω)
        (show Continuous (fun _ : ℝ≥0 ↦ X 0 ω) from continuous_const) (ne_of_gt ht)
    change ‖jumpProcess (X - fun _ : ℝ≥0 ↦ X 0) t ω‖ ≤ C
    rw [hcω.jumpProcess_sub hc0 t, hz, sub_zero]
    exact hjω t ht
  let τ := cappedNormExitSequence Y
  let σ : ℕ → Ω → WithTop ℝ≥0 := initialValueLocalizer (X 0) ⊓ τ
  have hτ : IsLocalizingSequence F τ P :=
    hY.1.isLocalizingSequence_cappedNormExitSequence hF hY.2.1
  have hstop (n : ℕ) : IsStoppingTime F (σ n) :=
    (initialValueLocalizer_isStoppingTime (hX.1 0) n).min (hτ.isStoppingTime n)
  have hmono : Monotone σ :=
    (initialValueLocalizer_monotone (X 0)).inf (monotone_cappedNormExitSequence Y)
  have hpre : IsPreLocalizingSequence F σ P := ⟨hstop, by
    filter_upwards [hτ.tendsto_top] with ω hω
    exact (initialValueLocalizer_tendsto (X 0) ω).min hω⟩
  have hcenter := hY.2.1.ae_norm_stoppedProcess_cappedNormExitSequence_le_of_jump_bound
    hY0 hC hjY
  have hb (n : ℕ) : ∀ᵐ ω ∂P, ∀ t, ‖MeasureTheory.stoppedProcess
      (fun s ↦ {ω | 0 < σ n ω}.indicator (X s)) (σ n) t ω‖ ≤ 2 * (n : ℝ) + 1 + C := by
    filter_upwards [hcenter] with ω hω t
    rw [stoppedProcess_indicator_comm]
    by_cases hp : 0 < σ n ω
    · rw [indicator_of_mem (show ω ∈ {ω | 0 < σ n ω} from hp)]
      have hi : |X 0 ω| ≤ (n : ℝ) := by
        by_contra hn
        have hle : σ n ω ≤ initialValueLocalizer (X 0) n ω := min_le_left _ _
        simp only [initialValueLocalizer, if_neg hn] at hle
        exact (not_le.mpr hp) hle
      let u : ℝ≥0 := (min (t : WithTop ℝ≥0) (σ n ω)).untopA
      have hne : min (t : WithTop ℝ≥0) (σ n ω) ≠ ⊤ :=
        ne_top_of_le_ne_top WithTop.coe_ne_top (min_le_left _ _)
      have hu : (u : WithTop ℝ≥0) ≤ cappedNormExitSequence Y n ω := by
        dsimp only [u]
        rw [WithTop.untopA_eq_untop hne, WithTop.coe_untop]
        exact (min_le_right _ _).trans (min_le_right _ _)
      have hy : ‖X u ω - X 0 ω‖ ≤ ((n + 1 : ℕ) : ℝ) + C := by
        simpa only [stoppedProcess_eq_of_le hu] using hω n u
      change ‖X u ω‖ ≤ 2 * (n : ℝ) + 1 + C
      calc
        _ = ‖(X u ω - X 0 ω) + X 0 ω‖ := by rw [sub_add_cancel]
        _ ≤ ‖X u ω - X 0 ω‖ + ‖X 0 ω‖ := norm_add_le _ _
        _ ≤ (((n + 1 : ℕ) : ℝ) + C) + n :=
          add_le_add hy (by simpa only [Real.norm_eq_abs] using hi)
        _ = _ := by push_cast; ring
    · rw [indicator_of_notMem (show ω ∉ {ω | 0 < σ n ω} from hp), norm_zero]
      positivity
  let B (n : ℕ) : ℝ≥0 := ⟨2 * (n : ℝ) + 1 + C, by positivity⟩
  have hui (n : ℕ) : IsUIMartingale (MeasureTheory.stoppedProcess
      (fun s ↦ {ω | 0 < σ n ω}.indicator (X s)) (σ n)) F P :=
    (hX.masked_stoppedProcess hF (hstop n)).isUIMartingale_of_bound (B n) (hb n)
  refine ⟨σ, ⟨hpre, hmono, hui⟩, fun n ↦ ⟨hb n, (hui n).1, fun t ↦ ?_⟩⟩
  exact MemLp.of_bound ((hui n).1.integrable t).aestronglyMeasurable (B n : ℝ)
    ((hb n).mono fun _ hω ↦ hω t)

/-- Bounded positive-time jumps imply the native locally square-integrable
martingale property, without any moment condition on the original initial value. -/
theorem IsLocalMartingale.locally_squareIntegrableMartingale_of_jump_bound
    (hX : IsLocalMartingale X F P) (hF : F.IsUsual P)
    (hC : 0 ≤ C) (hj : ∀ᵐ ω ∂P, ∀ t : ℝ≥0, 0 < t → ‖jumpProcess X t ω‖ ≤ C) :
    Locally (fun Y ↦ IsSquareIntegrableMartingale Y F P) F X P := by
  obtain ⟨τ, hτ, hb⟩ := hX.exists_bounded_fundamentalSequence_of_jump_bound hF hC hj
  exact ⟨τ, hτ.isLocalizingSequence, fun n ↦ (hb n).2⟩

end ProbabilityTheory
