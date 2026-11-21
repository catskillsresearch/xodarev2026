/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.Measurability.CagladVersion
public import StochLean.Probability.Process.Path.CagladBounded
public import StochLean.Probability.Process.Semimartingale.SimplePredictable.FirstExitTruncation
public import Mathlib.Probability.Process.LocalProperty
public import Mathlib.Topology.Order.Compact

/-! # Bounded masked cutoffs of adapted caglad processes

Open norm exits need not attain their target. Compact path bounds prove divergence
without an attainment claim. The closed cutoff remains bounded at a positive exit
by left continuity; the initial mask handles arbitrary initial values.
-/

@[expose] public section

open MeasureTheory Filter Set
open scoped NNReal Topology

namespace ProbabilityTheory

variable {Ω : Type*} {H : ℝ≥0 → Ω → ℝ}

theorem norm_firstExitTruncation_le {a : ℝ} (ha : 0 ≤ a) {ω : Ω}
    (hl : IsLeftContinuousPath (H · ω)) (t : ℝ≥0) :
    ‖firstExitTruncation H a t ω‖ ≤ a := by
  classical
  by_cases hpos : (0 : WithTop ℝ≥0) < hittingAfter H {x | a < ‖x‖} 0 ω
  · rw [firstExitTruncation, indicator_of_mem
      (show ω ∈ {v | (0 : WithTop ℝ≥0) < hittingAfter H {x | a < ‖x‖} 0 v} from hpos)]
    by_cases ht : (t : WithTop ℝ≥0) ≤ hittingAfter H {x | a < ‖x‖} 0 ω
    · simp only [cutoffIntegrand, if_pos ht]
      exact norm_le_of_le_hittingAfter_norm_of_pos hl hpos ht
    · simpa only [cutoffIntegrand, if_neg ht, norm_zero] using ha
  · simpa only [firstExitTruncation, indicator_of_notMem
      (show ω ∉ {v | (0 : WithTop ℝ≥0) < hittingAfter H {x | a < ‖x‖} 0 v} from hpos),
      norm_zero] using ha

theorem hittingAfter_norm_mono : Monotone (fun a : ℝ ↦ hittingAfter H {x | a < ‖x‖} 0) := by
  intro a b hab
  exact hittingAfter_anti H 0 (fun _ hx ↦ hab.trans_lt hx)

theorem IsCagladPath.tendsto_hittingAfter_norm_nat {ω : Ω}
    (hH : IsCagladPath (H · ω)) :
    Tendsto (fun n : ℕ ↦ hittingAfter H {x | (n : ℝ) < ‖x‖} 0 ω) atTop (𝓝 ⊤) := by
  rw [WithTop.tendsto_nhds_top_iff]
  intro T
  obtain ⟨C, _, hC⟩ := hH.exists_norm_bound_Icc (T + 1)
  obtain ⟨N, hN⟩ := exists_nat_gt C
  filter_upwards [eventually_ge_atTop N] with n hn
  have hbound : (T + 1 : ℝ≥0) ≤ hittingAfter H {x | (n : ℝ) < ‖x‖} 0 ω := by
    by_contra h
    obtain ⟨t, ht, hhit⟩ := hittingAfter_lt_iff.mp (lt_of_not_ge h)
    have htC := hC t ⟨ht.1, ht.2.le⟩
    exact (not_lt_of_ge htC) (hN.trans_le (Nat.cast_le.mpr hn) |>.trans hhit)
  exact (WithTop.coe_lt_coe.mpr (lt_add_one T)).trans_le hbound

end ProbabilityTheory

namespace MeasureTheory

open ProbabilityTheory

theorem Adapted.exists_bounded_caglad_cutoffSequence
    {Ω : Type*} {mΩ : MeasurableSpace Ω} {F : Filtration ℝ≥0 mΩ}
    {P : Measure Ω} {H : ℝ≥0 → Ω → ℝ}
    (ha : Adapted F H) (hF : F.IsUsual P) (hr : HasCagladPaths H P) :
    ∃ τ : ℕ → Ω → WithTop ℝ≥0, IsLocalizingSequence F τ P ∧ Monotone τ ∧
      ∀ n, ∀ᵐ ω ∂P, ∀ t, ‖{v | 0 < τ n v}.indicator (cutoffIntegrand H (τ n) t) ω‖ ≤ (n : ℝ) := by
  classical
  obtain ⟨K, heq, haK, hrK⟩ := ha.exists_caglad_indistinguishable_of_usual hF hr
  let τ : ℕ → Ω → WithTop ℝ≥0 := fun n ↦ hittingAfter K {x | (n : ℝ) < ‖x‖} 0
  have hmono : Monotone τ := fun _ _ hnm ↦ hittingAfter_norm_mono (Nat.cast_le.mpr hnm)
  let : F.IsRightContinuous := hF.rightContinuous
  refine ⟨τ, ⟨⟨fun n ↦ haK.isStoppingTime_hittingAfter_isOpen_of_leftContinuous
    (fun ω ↦ (hrK ω).1) (isOpen_lt continuous_const continuous_norm) 0,
    ae_of_all _ fun ω ↦ (hrK ω).tendsto_hittingAfter_norm_nat⟩,
    ae_of_all _ fun _ _ _ hnm ↦ hmono hnm _⟩, hmono, ?_⟩
  intro n
  filter_upwards [heq] with ω hω t
  have he : cutoffIntegrand H (τ n) t ω = cutoffIntegrand K (τ n) t ω := by
    simp only [cutoffIntegrand, hω]
  by_cases hp : 0 < τ n ω
  · rw [indicator_of_mem (show ω ∈ {v | 0 < τ n v} from hp), he]
    have hb := norm_firstExitTruncation_le (Nat.cast_nonneg n) (hrK ω).1 t
    change ‖{v | 0 < τ n v}.indicator (cutoffIntegrand K (τ n) t) ω‖ ≤ (n : ℝ) at hb
    simpa only [indicator_of_mem (show ω ∈ {v | 0 < τ n v} from hp)] using hb
  · simpa only [indicator_of_notMem (show ω ∉ {v | 0 < τ n v} from hp), norm_zero]
      using (Nat.cast_nonneg n : (0 : ℝ) ≤ n)

end MeasureTheory
