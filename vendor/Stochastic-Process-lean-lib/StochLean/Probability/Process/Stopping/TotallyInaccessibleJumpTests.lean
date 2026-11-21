/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.Stopping.LargeJumpSequence
public import StochLean.Probability.Process.Measurability.CadlagVersion

/-! # Totally inaccessible jumps from actual predictable jump tests

For an adapted process with almost-sure cadlag paths under usual
conditions, vanishing positive-time jumps at each predictable testing
lifetime imply the existing countable totally-inaccessible-jump property.
The exceptional event may depend on the testing lifetime: no common event
for all predictable tests is assumed or constructed.

An actual everywhere-cadlag indistinguishable version permits the existing
large-jump sequences to be used as genuine stopping times. Every finite
entry is a positive-time nonzero jump, so the test hypothesis proves each
entry totally inaccessible. The countably many positive thresholds cover
all nonzero positive jumps. Finally indistinguishability transports this
actual countable coverage back to the original process.

No finite-measure hypothesis, initial-value restriction, new stopping-time
selector, or graph-classification converse is needed.
-/

@[expose] public section

open ProbabilityTheory Filter Set
open scoped NNReal

namespace MeasureTheory

/-- An adapted cadlag process under usual conditions has totally
inaccessible positive jumps if each predictable testing lifetime sees zero
positive-time jump almost surely. Each test has its own permissible null set. -/
theorem Adapted.hasTotallyInaccessibleJumps_of_predictable_tests
    {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
    {F : Filtration ℝ≥0 mΩ} {X : ℝ≥0 → Ω → ℝ}
    (ha : Adapted F X) (hF : F.IsUsual P) (hc : HasCadlagPaths X P)
    (hzero : ∀ σ : Ω → WithTop ℝ≥0, IsPredictableStoppingTime F σ P →
      ∀ᵐ ω ∂P, ∀ t : ℝ≥0, 0 < t → σ ω = (t : WithTop ℝ≥0) →
        jumpProcess X t ω = 0) :
    HasTotallyInaccessibleJumps F X P := by
  classical
  let : F.IsRightContinuous := hF.rightContinuous
  obtain ⟨Y, hXY, hY, hcY⟩ :=
    ha.stronglyAdapted.exists_cadlag_indistinguishable_of_usual hF hc
  let b (k : ℕ) : ℝ := 1 / ((k : ℝ) + 1)
  have hb (k : ℕ) : 0 < b k := by dsimp only [b]; positivity
  let τ (k n : ℕ) : Ω → WithTop ℝ≥0 := largeJumpSequence Y (b k) n
  have hτ (k n : ℕ) : IsStoppingTime F (τ k n) :=
    hY.stronglyAdapted.adapted.isStoppingTime_largeJumpSequence hcY (hb k) n
  have hTI (k n : ℕ) : IsTotallyInaccessibleStoppingTime F (τ k n) P := by
    refine ⟨hτ k n, fun σ hσ ↦ ?_⟩
    have hnull : ∀ᵐ ω ∂P, ¬ (τ k n ω = σ ω ∧ τ k n ω ≠ ⊤) := by
      filter_upwards [hzero σ hσ, hXY.jumpProcess] with ω hz hXYω
      rintro ⟨he, hfin⟩
      cases hn : τ k n ω with
      | top => exact (hfin hn).elim
      | coe t =>
          have hgraph := (hcY ω).largeJumpSequence_mem_of_eq_coe (hb k) hn
          have hjzero : jumpProcess Y t ω = 0 :=
            (hXYω t).symm.trans (hz t hgraph.1 (he.symm.trans hn))
          have hb0 : b k < 0 := by
            simpa only [hjzero, norm_zero] using hgraph.2
          exact (not_lt_of_ge (hb k).le) hb0
    simpa only [not_not] using ae_iff.mp hnull
  have hJY : HasTotallyInaccessibleJumps F Y P := by
    refine ⟨fun i ↦ τ i.unpair.1 i.unpair.2, fun i ↦ hTI _ _, ?_⟩
    exact ae_of_all _ fun ω t ht hj ↦ by
      obtain ⟨k, hk⟩ := exists_nat_one_div_lt (norm_pos_iff.mpr hj)
      obtain ⟨n, hn⟩ := (hcY ω).exists_largeJumpSequence_eq (hb k) ht hk
      refine ⟨Nat.pair k n, ?_⟩
      simpa only [τ, Nat.unpair_pair] using hn
  exact hJY.congr hXY.symm

end MeasureTheory
