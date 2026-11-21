/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.UCP.ConsistentLocalization
public import StochLean.Probability.Process.UCP.Complete

/-! # Cadlag UCP limits of consistent localized processes

The generic UCP completion already constructs an adapted cadlag limit from a
UCP-Cauchy sequence.  For a stopped-consistent family, stopping continuity and
UCP uniqueness identify every localization of that limit with the prescribed
local process.  Unlike the predictable specialization, no null-set reset is
needed here.
-/

@[expose] public section

open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsFiniteMeasure P]
  {F : Filtration ℝ≥0 mΩ} {τ : ℕ → Ω → WithTop ℝ≥0}
  {A : ℕ → ℝ≥0 → Ω → ℝ}

/-- A stopped-consistent family of adapted cadlag processes has an adapted,
everywhere-cadlag UCP limit.  Stopping recovers every local level, and on one
common full-measure event the family is eventually equal to the limit on each
compact time interval. -/
theorem IsPreLocalizingSequence.exists_cadlag_limit_of_stopped_consistency
    (hτ : IsPreLocalizingSequence F τ P) (hF : F.IsUsual P)
    (ha : ∀ n, Adapted F (A n)) (hc : ∀ n, HasCadlagPaths (A n) P)
    (hcons : ∀ n m, n ≤ m → Indistinguishable (stoppedProcess (A m) (τ n)) (A n) P) :
    ∃ Y : ℝ≥0 → Ω → ℝ,
      Adapted F Y ∧ (∀ ω, IsCadlagPath (Y · ω)) ∧ TendstoUCP P A atTop Y ∧
      (∀ n, Indistinguishable (stoppedProcess Y (τ n)) (A n) P) ∧
      ∀ᵐ ω ∂P, ∀ T : ℝ≥0, ∀ᶠ n in atTop, ∀ t ≤ T, A n t ω = Y t ω := by
  have hC := hτ.cauchyUCP_of_stopped_consistency hcons
  obtain ⟨Y, hYa, hYc, hAY⟩ := hC.exists_adapted_cadlag_limit ha hF hc
  have hrY : HasRightContinuousPaths Y P := Eventually.of_forall fun ω ↦ (hYc ω).1
  have hstop : ∀ n, Indistinguishable (stoppedProcess Y (τ n)) (A n) P := by
    intro n
    have hs : TendstoUCP P (fun k : ℕ ↦ stoppedProcess (A (k + n)) (τ n)) atTop
        (stoppedProcess Y (τ n)) :=
      (hAY.comp (tendsto_add_atTop_nat n)).stoppedProcess (τ n)
    have he : TendstoUCP P (fun k : ℕ ↦ stoppedProcess (A (k + n)) (τ n)) atTop
        (A n) :=
      (tendstoUCP_const (P := P) atTop (A n)).congr_left
        (fun k ↦ (hcons n (k + n) (Nat.le_add_left n k)).symm)
    exact hs.indistinguishable_unique he (hrY.stoppedProcess (τ n))
      (hc n).hasRightContinuousPaths
  refine ⟨Y, hYa, hYc, hAY, hstop, ?_⟩
  filter_upwards [ae_all_iff.mpr hstop, hτ.tendsto_top] with ω hω hτω T
  filter_upwards [hτω.eventually (Ioi_mem_nhds (WithTop.coe_lt_top T))] with n hn
  intro t ht
  have htime : (t : WithTop ℝ≥0) ≤ τ n ω :=
    (WithTop.coe_le_coe.mpr ht).trans hn.le
  have he := hω n t
  rw [stoppedProcess_eq_of_le htime] at he
  exact he.symm

end ProbabilityTheory
