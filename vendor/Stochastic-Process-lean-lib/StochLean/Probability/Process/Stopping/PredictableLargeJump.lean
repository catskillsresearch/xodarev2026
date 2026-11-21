/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.FiniteVariation.DisjointPredictableJumps
public import StochLean.Probability.Process.FiniteVariation.IntegrableJumps
public import StochLean.Probability.Process.Stopping.AnnouncingInfimum
public import StochLean.Probability.Process.Stopping.PredictableRestriction
public import StochLean.Probability.Process.Stopping.Usual

/-! # The first large jump of a predictable FV process

The original `nextLargeJump` after zero is predictable. Its actual predictable
jump cover is restricted using the before-measurable, zero-terminal jump
coefficients. The resulting countable infimum agrees almost surely with the
original first large jump and, whenever finite, is attained by the cadlag first
jump property. Initial completeness transfers the constructed announcing data
back to the original lifetime. No new jump-time selector, initial moment, or
predictable-graph converse is used.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal Topology

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {F : Filtration ℝ≥0 mΩ}
  {P : Measure Ω}

private theorem predictable_congr_ae_of_usual {σ τ : Ω → WithTop ℝ≥0}
    (hσ : IsPredictableStoppingTime F σ P) (hF : F.IsUsual P)
    (he : σ =ᵐ[P] τ) : IsPredictableStoppingTime F τ P := by
  classical
  obtain ⟨ρ, hρ⟩ := hσ.2
  let G : Set Ω := {ω | σ ω = τ ω}
  have hGae : ∀ᵐ ω ∂P, ω ∈ G := he
  have hG : MeasurableSet[F 0] G := by
    have hGc : MeasurableSet[F 0] Gᶜ := hF.complete_initial _ (ae_iff.mp hGae)
    simpa only [compl_compl] using hGc.compl
  let π (n : ℕ) : Ω → WithTop ℝ≥0 := G.piecewise (ρ n) (fun _ ↦ 0)
  have hπ (n : ℕ) : IsStoppingTime F (π n) :=
    (hρ.isStoppingTime n).piecewise_of_le (isStoppingTime_const F 0)
      (fun _ ↦ bot_le) (fun _ ↦ bot_le) hG
  refine ⟨hσ.1.congr_ae_of_usual hF he, π, hπ, fun ω n m hnm ↦ ?_,
    fun n ω ht ↦ ?_, ?_⟩
  · by_cases hω : ω ∈ G
    · simpa only [π, Set.piecewise, if_pos hω] using hρ.monotone ω hnm
    · simp only [π, Set.piecewise, if_neg hω, le_refl]
  · by_cases hω : ω ∈ G
    · simp only [π, Set.piecewise, if_pos hω]
      have heω : σ ω = τ ω := hω
      simpa only [heω] using hρ.strict n ω (heω.symm ▸ ht)
    · simpa only [π, Set.piecewise, if_neg hω] using ht
  · filter_upwards [hGae, hρ.tendsto] with ω hω hl
    have heω : σ ω = τ ω := hω
    simpa only [π, Set.piecewise, if_pos hω, heω] using hl

end ProbabilityTheory

namespace MeasureTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {F : Filtration ℝ≥0 mΩ}
  {P : Measure Ω} [IsProbabilityMeasure P] {A : ℝ≥0 → Ω → ℝ} {b : ℝ}

/-- The first actual positive-time jump larger than a positive threshold is
predictable for a predictable cadlag FV process. The path hypotheses are only
almost sure, and no integrability of either the initial value or variation is
required. Infinite lifetimes remain infinite. -/
theorem IsStronglyPredictable.isPredictableStoppingTime_nextLargeJump_zero
    (hA : IsStronglyPredictable F A) (hF : F.IsUsual P)
    (hc : HasCadlagPaths A P) (hv : HasFiniteVariationPaths A P) (hb : 0 < b) :
    IsPredictableStoppingTime F (nextLargeJump A b (fun _ ↦ 0)) P := by
  classical
  obtain ⟨ρ, hρ, hpos, _, hcover⟩ :=
    hA.exists_positive_disjoint_predictableStoppingTime_cover_jumps hF hc hv
  let J (i : ℕ) : Ω → ℝ :=
    stoppedValueWithTerminal (jumpProcess A) (fun _ ↦ (0 : ℝ)) (ρ i)
  let D (i : ℕ) : Set Ω := {ω | b < ‖J i ω‖}
  let η (i : ℕ) := restrictedStoppingTime (ρ i) (D i)
  let T : Ω → WithTop ℝ≥0 := nextLargeJump A b (fun _ ↦ 0)
  have hmJ (i : ℕ) : StronglyMeasurable[(hρ i).1.measurableSpaceBefore] (J i) :=
    hA.stronglyMeasurable_stopped_jump_before_of_finiteVariation hF hc hv (hρ i).1
  have hmD (i : ℕ) : MeasurableSet[(hρ i).1.measurableSpaceBefore] (D i) :=
    measurableSet_lt measurable_const (hmJ i).norm.measurable
  have hη (i : ℕ) : IsPredictableStoppingTime F (η i) P :=
    (hρ i).restrictedStoppingTime_before hF (hmD i)
  have hηeq {i : ℕ} {ω : Ω} {t : ℝ≥0}
      (hi : ρ i ω = (t : WithTop ℝ≥0)) (hj : b < ‖jumpProcess A t ω‖) :
      η i ω = (t : WithTop ℝ≥0) := by
    have hωD : ω ∈ D i := by
      change b < ‖stoppedValueWithTerminal (jumpProcess A) (fun _ ↦ (0 : ℝ))
        (ρ i) ω‖
      rwa [stoppedValueWithTerminal_jump_eq_of_eq_coe hi]
    exact (restrictedStoppingTime_of_mem (ρ i) hωD).trans hi
  have hTη (i : ℕ) (ω : Ω) : T ω ≤ η i ω := by
    change T ω ≤ restrictedStoppingTime (ρ i) (D i) ω
    by_cases hωD : ω ∈ D i
    · rw [restrictedStoppingTime_of_mem (ρ i) hωD]
      cases ht : ρ i ω with
      | top => exact le_top
      | coe t =>
        apply nextLargeJump_le_of_jump (ht ▸ hpos i ω)
        change b < ‖J i ω‖ at hωD
        simpa only [J, stoppedValueWithTerminal_jump_eq_of_eq_coe ht] using hωD
    · rw [restrictedStoppingTime_of_notMem (ρ i) hωD]
      exact le_top
  have he : (fun ω ↦ ⨅ i, η i ω) =ᵐ[P] T := by
    filter_upwards [hcover] with ω hω
    apply le_antisymm ?_ (le_iInf fun i ↦ hTη i ω)
    change (⨅ i, η i ω) ≤ ⨅ t : ℝ≥0,
      ⨅ (_ : (0 : WithTop ℝ≥0) < t ∧ b < ‖jumpProcess A t ω‖), (t : WithTop ℝ≥0)
    apply le_iInf
    intro t
    apply le_iInf
    intro ht
    obtain ⟨i, hi⟩ := hω t (WithTop.coe_lt_coe.mp ht.1)
      (norm_pos_iff.mp (hb.trans ht.2))
    exact (iInf_le (fun i ↦ η i ω) i).trans_eq (hηeq hi ht.2)
  have hatt : ∀ᵐ ω ∂P, (⨅ i, η i ω) ≠ ⊤ → ∃ i, η i ω = ⨅ j, η j ω := by
    filter_upwards [hc, hcover, he] with ω hcω hω heω
    intro hn
    have hT : T ω ≠ ⊤ := fun ht ↦ hn (heω.trans ht)
    obtain ⟨t, ht, hpt, hj, _⟩ := hcω.nextLargeJump_spec hb hT
    obtain ⟨i, hi⟩ := hω t (WithTop.coe_lt_coe.mp hpt)
      (norm_pos_iff.mp (hb.trans hj))
    exact ⟨i, (hηeq hi hj).trans (ht.symm.trans heω.symm)⟩
  exact predictable_congr_ae_of_usual
    (IsPredictableStoppingTime.iInf_nat_of_ae_attained hη hF hatt) hF he

end MeasureTheory
