/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.Stopping.LargeJumpTimes
public import StochLean.Probability.Process.Stopping.Usual
public import StochLean.Probability.Process.Measurability.CadlagVersion
public import StochLean.Probability.Process.Path.RunningJumpSupremum
public import Mathlib.Probability.Process.LocalProperty

/-! # Localizing by the actual first jump above an increasing threshold

The existing `nextLargeJump` owner is monotone in its threshold for arbitrary
paths. For adapted AE-cadlag processes, an everywhere-cadlag version gives
stopping times, and usual completeness transfers that property to the original
lifetimes through common jump equality.

Every actual compact running jump supremum is finite on a cadlag path.
A finite first-jump value is attained, so thresholds tending to infinity
eventually force that first jump beyond any fixed horizon. This proves the
native localizing property of the original threshold sequence, without a
new jump-time selector, finite variation, predictability, an initial-value
bound, or a moment assumption. Threshold monotonicity holds everywhere.
-/

@[expose] public section

open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology

namespace ProbabilityTheory

variable {Ω : Type*} {X : ℝ≥0 → Ω → ℝ} {b c : ℝ}
  {σ : Ω → WithTop ℝ≥0} {ω : Ω}

/-- Raising the threshold cannot advance the actual next large jump.
No path regularity or measurability is required for this order property. -/
theorem nextLargeJump_mono_threshold (hbc : b ≤ c) :
    nextLargeJump X b σ ω ≤ nextLargeJump X c σ ω := by
  apply le_iInf
  intro t
  apply le_iInf
  intro ht
  exact nextLargeJump_le_of_jump ht.1 (hbc.trans_lt ht.2)

end ProbabilityTheory

namespace MeasureTheory

open ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
  {F : Filtration ℝ≥0 mΩ} {X : ℝ≥0 → Ω → ℝ}

/-- Actual first positive-time jumps above the thresholds `n + 1` form a
native localizing sequence. The original process needs only AE-cadlag paths;
no finiteness assumption on the ambient measure is used. -/
theorem Adapted.isLocalizingSequence_nextLargeJump_nat_threshold
    (ha : Adapted F X) (hF : F.IsUsual P) (hc : HasCadlagPaths X P) :
    IsLocalizingSequence F
      (fun n ↦ nextLargeJump X (((n + 1 : ℕ) : ℝ)) (fun _ ↦ 0)) P := by
  let : F.IsRightContinuous := hF.rightContinuous
  let τ (n : ℕ) := nextLargeJump X (((n + 1 : ℕ) : ℝ)) (fun _ ↦ 0)
  obtain ⟨Y, heXY, hpY, hcY⟩ :=
    ha.stronglyAdapted.exists_cadlag_indistinguishable_of_usual hF hc
  have hstop (n : ℕ) : IsStoppingTime F (τ n) := by
    have hY := hpY.stronglyAdapted.adapted.isStoppingTime_nextLargeJump hcY
      (show 0 < ((n + 1 : ℕ) : ℝ) from by positivity) (isStoppingTime_const F 0)
    apply hY.congr_ae_of_usual hF
    filter_upwards [heXY.jumpProcess] with ω hω
    simp only [τ, nextLargeJump, hω, WithTop.coe_zero]
  have hmono (ω : Ω) : Monotone (τ · ω) := by
    intro n m hnm
    apply nextLargeJump_mono_threshold
    exact_mod_cast Nat.succ_le_succ hnm
  have hlim : ∀ᵐ ω ∂P, Tendsto (τ · ω) atTop (𝓝 ⊤) := by
    filter_upwards [hc] with ω hcω
    apply (WithTop.tendsto_nhds_top_iff _).mpr
    intro T
    have hfin := hcω.eRunningJumpSupremum_ne_top T
    obtain ⟨m, hm⟩ := exists_nat_gt (eRunningJumpSupremum X T ω).toReal
    filter_upwards [eventually_ge_atTop m] with n hmn
    apply lt_of_not_ge
    intro hle
    have hτfin : τ n ω ≠ ⊤ := ne_top_of_le_ne_top WithTop.coe_ne_top hle
    obtain ⟨t, ht, _, hj, _⟩ := hcω.nextLargeJump_spec
      (show 0 < ((n + 1 : ℕ) : ℝ) from by positivity) hτfin
    have htT : t ≤ T := WithTop.coe_le_coe.mp (ht ▸ hle)
    have hjle : ‖jumpProcess X t ω‖ ≤ (eRunningJumpSupremum X T ω).toReal := by
      have he : ENNReal.ofReal ‖jumpProcess X t ω‖ ≤ eRunningJumpSupremum X T ω :=
        le_iSup_of_le t (le_iSup_of_le htT le_rfl)
      simpa only [ENNReal.toReal_ofReal (norm_nonneg _)] using ENNReal.toReal_mono hfin he
    have hmnR : (m : ℝ) ≤ n := by exact_mod_cast hmn
    have hn : (n : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.le_succ n
    linarith only [hj, hjle, hm, hmnR, hn]
  exact ⟨⟨hstop, hlim⟩, Eventually.of_forall hmono⟩

end MeasureTheory
