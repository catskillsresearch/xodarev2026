/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.Stopping.LargeJumpSequence
public import StochLean.Probability.Process.Stopping.ClassificationDecomposition
public import StochLean.Probability.Process.Measurability.CadlagVersion

/-! # Predictable coverage from the absence of totally inaccessible jumps

The explicit premise that the process has zero positive-time jumps at every
totally inaccessible stopping time is a prerequisite for this bridge, not a
proof of Protter III.14. The existing III.3 decomposition first makes any
stopping time carried by the nonzero positive jump graph accessible. Its
countable predictable cover need not make that stopping time itself predictable.

For an adapted cadlag process under usual conditions, the existing actual
large-jump sequences, at thresholds `1 / (k + 1)`, then give a common almost-sure
countable predictable cover of all nonzero positive-time jumps. Initial values
are unconstrained, and infinite times are never replaced by finite values.
-/

@[expose] public section

open MeasureTheory Filter Set
open scoped NNReal

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [SFinite P]
  {F : Filtration ℝ≥0 mΩ} {X : ℝ≥0 → Ω → ℝ} {τ : Ω → WithTop ℝ≥0}

/-- The actual III.3 decomposition turns a stopping time on the nonzero positive
jump graph into an accessible time when all totally inaccessible jump tests vanish. -/
theorem isAccessibleStoppingTime_of_no_totallyInaccessible_jumps
    (hτ : IsStoppingTime F τ)
    (hzero : ∀ ρ, IsTotallyInaccessibleStoppingTime F ρ P →
      ∀ᵐ ω ∂P, ∀ t : ℝ≥0, 0 < t → ρ ω = (t : WithTop ℝ≥0) →
        jumpProcess X t ω = 0)
    (hgraph : ∀ᵐ ω ∂P, τ ω ≠ ⊤ →
      ∃ t : ℝ≥0, 0 < t ∧ τ ω = (t : WithTop ℝ≥0) ∧ jumpProcess X t ω ≠ 0) :
    IsAccessibleStoppingTime F τ P := by
  obtain ⟨A, B, hd⟩ := exists_accessibleInaccessible_decomposition hτ P
  have hB : restrictedStoppingTime τ B =ᵐ[P] (fun _ ↦ ⊤) := by
    filter_upwards [hgraph, hzero _ hd.totallyInaccessible] with ω hω hz
    by_contra hf
    obtain ⟨hBω, hτf⟩ := (restrictedStoppingTime_ne_top_iff τ B ω).mp hf
    obtain ⟨t, ht, hτt, hj⟩ := hω hτf
    exact hj (hz t ht ((restrictedStoppingTime_of_mem τ hBω).trans hτt))
  have he : restrictedStoppingTime τ A =ᵐ[P] τ := by
    filter_upwards [hd.reconstruct, hB] with ω hr hb
    simpa only [hb, min_top_right] using hr
  obtain ⟨σ, hσ, hcover⟩ := hd.accessible.2
  refine ⟨hτ, σ, hσ, ?_⟩
  filter_upwards [he, hcover] with ω heω hω hf
  obtain ⟨n, hn⟩ := hω (fun htop ↦ hf (heω.symm.trans htop))
  exact ⟨n, heω.symm.trans hn⟩

end ProbabilityTheory

namespace MeasureTheory

open ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [SFinite P]
  {F : Filtration ℝ≥0 mΩ} {X : ℝ≥0 → Ω → ℝ}

/-- Actual cadlag jump enumeration and III.3 produce countably many predictable
times covering all nonzero positive-time jumps on one common full-measure event.
The input is a zero-jump test, not a supplied enumeration or a naturality certificate. -/
theorem Adapted.exists_predictableStoppingTime_cover_jumps_of_no_totallyInaccessible_jumps
    (ha : Adapted F X) (hF : F.IsUsual P) (hc : HasCadlagPaths X P)
    (hzero : ∀ ρ, IsTotallyInaccessibleStoppingTime F ρ P →
      ∀ᵐ ω ∂P, ∀ t : ℝ≥0, 0 < t → ρ ω = (t : WithTop ℝ≥0) →
        jumpProcess X t ω = 0) :
    ∃ σ : ℕ → Ω → WithTop ℝ≥0,
      (∀ n, IsPredictableStoppingTime F (σ n) P) ∧
        ∀ᵐ ω ∂P, ∀ t : ℝ≥0, 0 < t → jumpProcess X t ω ≠ 0 →
          ∃ n, σ n ω = (t : WithTop ℝ≥0) := by
  classical
  let : F.IsRightContinuous := hF.rightContinuous
  obtain ⟨Y, hXY, hY, hcY⟩ :=
    ha.stronglyAdapted.exists_cadlag_indistinguishable_of_usual hF hc
  have hzY (ρ : Ω → WithTop ℝ≥0) (hρ : IsTotallyInaccessibleStoppingTime F ρ P) :
      ∀ᵐ ω ∂P, ∀ t : ℝ≥0, 0 < t → ρ ω = (t : WithTop ℝ≥0) →
        jumpProcess Y t ω = 0 := by
    filter_upwards [hzero ρ hρ, hXY.jumpProcess] with ω hz he
    intro t ht hρt
    exact (he t).symm.trans (hz t ht hρt)
  let b (k : ℕ) : ℝ := 1 / ((k : ℝ) + 1)
  have hb (k : ℕ) : 0 < b k := by dsimp only [b]; positivity
  have hacc (k n : ℕ) : IsAccessibleStoppingTime F (largeJumpSequence Y (b k) n) P := by
    apply isAccessibleStoppingTime_of_no_totallyInaccessible_jumps
      (hY.stronglyAdapted.adapted.isStoppingTime_largeJumpSequence hcY (hb k) n) hzY
    apply Eventually.of_forall
    intro ω hf
    cases hn : largeJumpSequence Y (b k) n ω with
    | top => exact (hf hn).elim
    | coe t =>
      have hj := (hcY ω).largeJumpSequence_mem_of_eq_coe (hb k) hn
      exact ⟨t, hj.1, rfl, norm_pos_iff.mp ((hb k).trans hj.2)⟩
  choose σ hσ hcover using fun k n ↦ (hacc k n).2
  have hall : ∀ᵐ ω ∂P, ∀ k n, largeJumpSequence Y (b k) n ω ≠ ⊤ →
      ∃ j, largeJumpSequence Y (b k) n ω = σ k n j ω :=
    ae_all_iff.mpr fun k ↦ ae_all_iff.mpr fun n ↦ hcover k n
  let θ : ℕ → Ω → WithTop ℝ≥0 := fun i ↦
    σ i.unpair.1 i.unpair.2.unpair.1 i.unpair.2.unpair.2
  refine ⟨θ, fun i ↦ hσ _ _ _, ?_⟩
  filter_upwards [hall, hXY.jumpProcess] with ω hω he
  intro t ht hj
  have hjY : jumpProcess Y t ω ≠ 0 := by
    rw [← he t]
    exact hj
  obtain ⟨k, hk⟩ := exists_nat_one_div_lt (norm_pos_iff.mpr hjY)
  obtain ⟨n, hn⟩ := (hcY ω).exists_largeJumpSequence_eq (hb k) ht hk
  obtain ⟨j, hj⟩ := hω k n (fun htop ↦ WithTop.coe_ne_top (hn.symm.trans htop))
  refine ⟨Nat.pair k (Nat.pair n j), ?_⟩
  simpa only [θ, Nat.unpair_pair] using hj.symm.trans hn

end MeasureTheory
