/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.Path.Cadlag
public import Mathlib.Topology.Order.MonotoneConvergence
public import Mathlib.Analysis.Normed.Group.Continuity
public import Mathlib.Topology.Order.WithTop

/-! # Separated samples of a cadlag path cannot accumulate in finite time

Infinitely many chronologically ordered samples with a fixed positive consecutive
oscillation must escape every finite horizon. The contradiction uses the actual
finite left limit at a hypothetical accumulation point, not a compactness assumption
about a space of paths.
-/

@[expose] public section

open Filter Set
open scoped NNReal Topology

namespace ProbabilityTheory

variable {E : Type*} [NormedAddCommGroup E] {x : ℝ≥0 → E}

theorem IsCadlagPath.tendsto_atTop_of_separated_samples (hx : IsCadlagPath x)
    {u : ℕ → ℝ≥0} (hu : StrictMono u) {ε : ℝ} (hε : 0 < ε)
    (hsep : ∀ n, ε ≤ ‖x (u (n + 1)) - x (u n)‖) : Tendsto u atTop atTop := by
  rcases tendsto_atTop_of_monotone hu.monotone with htop | ⟨T, hlim⟩
  · exact htop
  · have hlt (n : ℕ) : u n < T :=
      (hu (Nat.lt_succ_self n)).trans_le (hu.monotone.ge_of_tendsto hlim (n + 1))
    have hT : T ≠ (0 : ℝ≥0) := ne_of_gt ((bot_le : (0 : ℝ≥0) ≤ u 0).trans_lt (hlt 0))
    obtain ⟨y, hy⟩ := hx.2 T hT
    have hwithin : Tendsto u atTop (𝓝[<] T) :=
      tendsto_nhdsWithin_iff.mpr ⟨hlim, Eventually.of_forall hlt⟩
    have hxu : Tendsto (fun n ↦ x (u n)) atTop (𝓝 y) := hy.comp hwithin
    have hdiff : Tendsto (fun n ↦ ‖x (u (n + 1)) - x (u n)‖) atTop (𝓝 0) := by
      simpa only [Function.comp_def, sub_self, norm_zero] using
        ((hxu.comp (tendsto_add_atTop_nat 1)).sub hxu).norm
    exact (not_le_of_gt hε (ge_of_tendsto' hdiff hsep)).elim

theorem IsCadlagPath.tendsto_top_of_separated_extended_samples (hx : IsCadlagPath x)
    {τ : ℕ → WithTop ℝ≥0} (hmono : Monotone τ)
    (hstrict : ∀ n, τ (n + 1) ≠ ⊤ → τ n < τ (n + 1)) {ε : ℝ} (hε : 0 < ε)
    (hsep : ∀ n, τ (n + 1) ≠ ⊤ → ε ≤ ‖x (τ (n + 1)).untopA - x (τ n).untopA‖) :
    Tendsto τ atTop (𝓝 ⊤) := by
  classical
  by_cases hex : ∃ N, τ N = ⊤
  · obtain ⟨N, hN⟩ := hex
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_ge_atTop N] with n hn
    exact le_antisymm (by rw [← hN]; exact hmono hn) le_top
  · have hne (n : ℕ) : τ n ≠ ⊤ := fun h ↦ hex ⟨n, h⟩
    let u : ℕ → ℝ≥0 := fun n ↦ (τ n).untopA
    have heq (n : ℕ) : (u n : WithTop ℝ≥0) = τ n := by
      change ((τ n).untopA : WithTop ℝ≥0) = τ n
      rw [WithTop.untopA_eq_untop (hne n), WithTop.coe_untop]
    have hu : StrictMono u := by
      apply strictMono_nat_of_lt_succ
      intro n
      apply WithTop.coe_lt_coe.mp
      rw [heq, heq]
      exact hstrict n (hne (n + 1))
    have hlim := hx.tendsto_atTop_of_separated_samples hu hε (fun n ↦ hsep n (hne (n + 1)))
    have hcoe := WithTop.tendsto_coe_atTop.comp hlim
    change Tendsto (fun n ↦ (u n : WithTop ℝ≥0)) atTop (𝓝 ⊤) at hcoe
    simpa only [heq] using hcoe

end ProbabilityTheory
