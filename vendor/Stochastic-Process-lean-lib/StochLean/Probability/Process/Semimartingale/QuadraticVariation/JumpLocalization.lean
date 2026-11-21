/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.Semimartingale.QuadraticVariation.JumpBound
public import StochLean.Probability.Process.Stopping.CagladLocalization
public import StochLean.Probability.Process.LocalMartingale.Reducing
public import StochLean.Probability.Process.LocalMartingale.Bounded
public import StochLean.Probability.Moments.L2

/-! # L2 localization from integrable raw quadratic variation

The left-limit process is localized by bounded caglad cutoffs. Every stopped
jump, including the initial jump, is controlled by the actual raw bracket.
The resulting masked stopped local martingales have L2 envelopes on each
finite horizon, so the source envelope criterion makes them true L2 martingales.
An actual semimartingale witness is explicit until the general LM-to-SM theorem
is available; this result does not assume the desired true-martingale property.
-/

@[expose] public section

open MeasureTheory Set
open scoped NNReal ENNReal

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsFiniteMeasure P]
  {F : Filtration ℝ≥0 mΩ} {X : ℝ≥0 → Ω → ℝ}

theorem IsSemimartingale.memLp_sqrt_quadraticVariation
    (hX : IsSemimartingale X F P) (hF : F.IsUsual P) {T : ℝ≥0}
    (hQ : Integrable (hX.quadraticVariation hF T) P) :
    MemLp (fun ω ↦ Real.sqrt (hX.quadraticVariation hF T ω)) 2 P := by
  have hm := ((hX.adapted_quadraticVariation hF T).mono (F.le T) le_rfl).sqrt
  apply (memLp_two_iff_integrable_sq hm.aestronglyMeasurable).mpr
  apply hQ.congr
  filter_upwards [hX.initial_sq_le_quadraticVariation hF] with ω hω
  exact (Real.sq_sqrt ((sq_nonneg _).trans (hω T))).symm

/-- An integrable raw bracket at any finite horizon controls the unmasked
initial value, because the raw bracket includes its initial square. -/
theorem IsSemimartingale.memLp_initial_of_integrable_quadraticVariation
    (hX : IsSemimartingale X F P) (hF : F.IsUsual P) {T : ℝ≥0}
    (hQ : Integrable (hX.quadraticVariation hF T) P) : MemLp (X 0) 2 P := by
  apply (hX.memLp_sqrt_quadraticVariation hF hQ).mono'
    (((hX.adapted 0).mono (F.le 0) le_rfl).aestronglyMeasurable)
  filter_upwards [hX.norm_jump_le_sqrt_quadraticVariation hF] with ω hω
  simpa only [jumpProcess_zero] using hω 0 T bot_le

variable [SigmaFiniteFiltration P F]

/-- The stopped localizers are constructed, and their L2 and true-martingale
properties are proved from the actual bracket moment assumption. -/
theorem IsSemimartingale.locally_squareIntegrableMartingale_of_integrable_quadraticVariation
    (hX : IsSemimartingale X F P) (hF : F.IsUsual P) (hM : IsLocalMartingale X F P)
    (hQ : ∀ T, Integrable (hX.quadraticVariation hF T) P) :
    Locally (fun Y ↦ IsSquareIntegrableMartingale Y F P) F X P := by
  classical
  obtain ⟨τ, hτ, _, hb⟩ := Adapted.exists_bounded_caglad_cutoffSequence
    (hX.adapted.leftLimitProcess_of_usual hF hX.hasCadlagPaths)
      hF hX.hasCadlagPaths.hasCagladPaths_leftLimitProcess
  refine ⟨τ, hτ, fun n ↦ ?_⟩
  let Y := MeasureTheory.stoppedProcess (fun t ↦ {ω | 0 < τ n ω}.indicator (X t)) (τ n)
  have hY : IsLocalMartingale Y F P := hM.masked_stoppedProcess hF (hτ.isStoppingTime n)
  let g (T : ℝ≥0) (ω : Ω) := (n : ℝ) + Real.sqrt (hX.quadraticVariation hF T ω)
  have hglp (T : ℝ≥0) : MemLp (g T) 2 P :=
    (memLp_const (n : ℝ)).add (hX.memLp_sqrt_quadraticVariation hF (hQ T))
  have hYb (T : ℝ≥0) : ∀ᵐ ω ∂P, ∀ t ≤ T, ‖Y t ω‖ ≤ g T ω := by
    filter_upwards [hb n, hX.norm_jump_le_sqrt_quadraticVariation hF] with ω hH hj t ht
    change ‖MeasureTheory.stoppedProcess
      (fun t ↦ {ω | 0 < τ n ω}.indicator (X t)) (τ n) t ω‖ ≤ g T ω
    rw [stoppedProcess_indicator_comm]
    by_cases hp : 0 < τ n ω
    · rw [indicator_of_mem (show ω ∈ {v | 0 < τ n v} from hp)]
      let s := (min (t : WithTop ℝ≥0) (τ n ω)).untopA
      have hst : s ≤ t := WithTop.untopA_le (min_le_left _ _)
      have hsτ : (s : WithTop ℝ≥0) ≤ τ n ω :=
        (WithTop.coe_untopD_le _ _).trans (min_le_right _ _)
      have hHs := hH s
      rw [indicator_of_mem (show ω ∈ {v | 0 < τ n v} from hp),
        cutoffIntegrand, if_pos hsτ] at hHs
      change ‖X s ω‖ ≤ (n : ℝ) + Real.sqrt (hX.quadraticVariation hF T ω)
      calc
        _ = ‖leftLimitProcess X s ω + jumpProcess X s ω‖ := by
          congr 1
          simp only [jumpProcess, Pi.sub_apply]
          ring
        _ ≤ ‖leftLimitProcess X s ω‖ + ‖jumpProcess X s ω‖ := norm_add_le _ _
        _ ≤ _ := add_le_add hHs (hj s T (hst.trans ht))
    · rw [indicator_of_notMem (show ω ∉ {v | 0 < τ n v} from hp), norm_zero]
      exact add_nonneg (Nat.cast_nonneg n) (Real.sqrt_nonneg _)
  refine ⟨hY.martingale_of_integrable_envelope (fun T ↦
    ⟨g T, (hglp T).integrable (by norm_num), hYb T⟩), fun T ↦ ?_⟩
  exact (hglp T).mono' (((hY.1 T).mono (F.le T) le_rfl).aestronglyMeasurable)
    ((hYb T).mono fun _ hω ↦ hω T le_rfl)

end ProbabilityTheory
