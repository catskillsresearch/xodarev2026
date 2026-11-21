/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.Stopping.LargeJumpSequence
public import StochLean.Probability.Process.Stopping.ClassificationDecomposition
public import StochLean.Probability.Process.Stopping.PredictableDisjointGraphs
public import StochLean.Probability.Process.Measurability.CadlagVersion

/-! # A predictable sequence covering every predictable jump test

For an adapted cadlag process, the existing large-jump sequences enumerate
the actual positive jumps of an everywhere cadlag indistinguishable version.
Each enumerating stopping time has the actual accessible/totally inaccessible
decomposition from Protter III.3. Flattening the accessible predictable covers
and applying the existing positive disjoint graph restriction theorem gives
one positive predictable sequence.

For each fixed predictable testing lifetime, its finite graph avoids all of
the countably many totally inaccessible components almost surely. Its nonzero
positive-time jumps are therefore covered by this sequence. The quantifier
order is essential: the almost-sure event may depend on the test lifetime.
No common event covering every random predictable test is asserted.

The resulting predictable graphs may contain points where the original
process does not jump, and no coefficient bound is asserted on these graphs.
In particular they are not restricted using a jump-amplitude event presumed
to be known before the lifetime. No predictability or finite variation of the
original process is required, and infinity has no finite graph point.
-/

@[expose] public section

open ProbabilityTheory Filter Set
open scoped NNReal

namespace MeasureTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsFiniteMeasure P]
  {F : Filtration ℝ≥0 mΩ} {X : ℝ≥0 → Ω → ℝ}

/-- One actual positive disjoint predictable sequence covers the nonzero
positive-time jump of every fixed predictable test, almost surely for that
test. The exceptional event is permitted to depend on the testing lifetime. -/
theorem Adapted.exists_positive_disjoint_predictableStoppingTime_cover_jump_tests
    (ha : Adapted F X) (hF : F.IsUsual P) (hc : HasCadlagPaths X P) :
    ∃ Γ : ℕ → Ω → WithTop ℝ≥0,
      (∀ n, IsPredictableStoppingTime F (Γ n) P) ∧
      (∀ n ω, 0 < Γ n ω) ∧
      Pairwise (fun n m ↦ Disjoint (stoppingTimeGraph (Γ n)) (stoppingTimeGraph (Γ m))) ∧
      ∀ γ : Ω → WithTop ℝ≥0, IsPredictableStoppingTime F γ P →
        ∀ᵐ ω ∂P, ∀ t : ℝ≥0, 0 < t → γ ω = (t : WithTop ℝ≥0) →
          jumpProcess X t ω ≠ 0 → ∃ n, Γ n ω = (t : WithTop ℝ≥0) := by
  classical
  let : F.IsRightContinuous := hF.rightContinuous
  obtain ⟨Y, hXY, hY, hcY⟩ :=
    ha.stronglyAdapted.exists_cadlag_indistinguishable_of_usual hF hc
  let b (k : ℕ) : ℝ := 1 / ((k : ℝ) + 1)
  have hb (k : ℕ) : 0 < b k := by dsimp only [b]; positivity
  let τ (k n : ℕ) : Ω → WithTop ℝ≥0 := largeJumpSequence Y (b k) n
  have hτ (k n : ℕ) : IsStoppingTime F (τ k n) :=
    hY.stronglyAdapted.adapted.isStoppingTime_largeJumpSequence hcY (hb k) n
  choose A B hd using fun k n ↦ exists_accessibleInaccessible_decomposition (hτ k n) P
  choose σ hσ hcover using fun k n ↦ (hd k n).accessible.2
  have hun (k n : ℕ) : ∀ᵐ ω ∂P,
      (ω ∈ A k n ∨ ω ∈ B k n) ↔ τ k n ω ≠ ⊤ := by
    filter_upwards [(hd k n).union_ae] with ω hω
    exact Iff.of_eq hω
  have hallCover : ∀ᵐ ω ∂P, ∀ k n,
      restrictedStoppingTime (τ k n) (A k n) ω ≠ ⊤ →
        ∃ j, restrictedStoppingTime (τ k n) (A k n) ω = σ k n j ω :=
    ae_all_iff.mpr fun k ↦ ae_all_iff.mpr fun n ↦ hcover k n
  have hallUnion : ∀ᵐ ω ∂P, ∀ k n,
      (ω ∈ A k n ∨ ω ∈ B k n) ↔ τ k n ω ≠ ⊤ :=
    ae_all_iff.mpr fun k ↦ ae_all_iff.mpr fun n ↦ hun k n
  let θ : ℕ → Ω → WithTop ℝ≥0 := fun i ↦
    σ i.unpair.1 i.unpair.2.unpair.1 i.unpair.2.unpair.2
  have hθ (i : ℕ) : IsPredictableStoppingTime F (θ i) P := hσ _ _ _
  obtain ⟨Γ, hΓ, hpΓ, _, hdΓ, huΓ⟩ :=
    exists_positive_predictableStoppingTime_disjoint_graph_restrictions θ hθ hF
  refine ⟨Γ, hΓ, hpΓ, hdΓ, ?_⟩
  intro γ hγ
  have hnull (k n : ℕ) : ∀ᵐ ω ∂P,
      ¬ (restrictedStoppingTime (τ k n) (B k n) ω = γ ω ∧
        restrictedStoppingTime (τ k n) (B k n) ω ≠ ⊤) := by
    rw [ae_iff]
    simpa only [not_not] using (hd k n).totallyInaccessible.2 γ hγ
  have hallNull : ∀ᵐ ω ∂P, ∀ k n,
      ¬ (restrictedStoppingTime (τ k n) (B k n) ω = γ ω ∧
        restrictedStoppingTime (τ k n) (B k n) ω ≠ ⊤) :=
    ae_all_iff.mpr fun k ↦ ae_all_iff.mpr fun n ↦ hnull k n
  filter_upwards [hallCover, hallUnion, hallNull, hXY.jumpProcess]
    with ω hcovω huω hnω hXYω t ht hγt hj
  have hjY : jumpProcess Y t ω ≠ 0 := by
    rw [← hXYω t]
    exact hj
  obtain ⟨k, hk⟩ := exists_nat_one_div_lt (norm_pos_iff.mpr hjY)
  obtain ⟨n, hnt⟩ := (hcY ω).exists_largeJumpSequence_eq (hb k) ht hk
  have hτt : τ k n ω = (t : WithTop ℝ≥0) := hnt
  have hf : τ k n ω ≠ ⊤ := fun he ↦ WithTop.coe_ne_top (hτt.symm.trans he)
  have hA : ω ∈ A k n := by
    rcases (huω k n).mpr hf with hA | hB
    · exact hA
    · have he := restrictedStoppingTime_of_mem (τ k n) hB
      exact (hnω k n ⟨he.trans (hτt.trans hγt.symm),
        fun htop ↦ hf (he.symm.trans htop)⟩).elim
  have heA := restrictedStoppingTime_of_mem (τ k n) hA
  obtain ⟨j, hjσ⟩ := hcovω k n (fun htop ↦ hf (heA.symm.trans htop))
  have hσt : σ k n j ω = (t : WithTop ℝ≥0) := hjσ.symm.trans (heA.trans hτt)
  have hθt : θ (Nat.pair k (Nat.pair n j)) ω = (t : WithTop ℝ≥0) := by
    simpa only [θ, Nat.unpair_pair] using hσt
  have hmem : (t, ω) ∈ ⋃ i, stoppingTimeGraph (Γ i) := by
    rw [huΓ]
    exact ⟨⟨ht, mem_univ ω⟩, mem_iUnion.mpr ⟨Nat.pair k (Nat.pair n j), hθt⟩⟩
  obtain ⟨i, hi⟩ := mem_iUnion.mp hmem
  exact ⟨i, hi⟩

end MeasureTheory
