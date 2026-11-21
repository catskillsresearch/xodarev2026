/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Independence.Completion
public import Mathlib.Topology.Order.IsLUB

/-! # Completing a right-continuous filtration

Adjoining every ambient null set preserves right continuity for nonnegative
real time. The proof chooses actual raw measurable representatives along
a decreasing sequence of future times. Their set limsup is measurable at
every future time and hence in the original right-continuous field.

This is a statement on the genuinely completed ambient space. It does not
assert completeness of the original space, nor identify a raw field with
its completion. No finiteness or probability assumption on the measure is
needed.
-/

@[expose] public section

open MeasureTheory Filter Set
open scoped NNReal Topology symmDiff

namespace ProbabilityTheory

/-- Adjoining ambient null sets adds exactly the almost-sure versions of
old measurable events, even when the old subfield is not complete. -/
theorem measurableSet_sup_nullSets_iff
    {Ω : Type*} {m mΩ : MeasurableSpace Ω} {P : Measure Ω} {E : Set Ω} :
    MeasurableSet[m ⊔ Filtration.nullSets P] E ↔
      ∃ B : Set Ω, MeasurableSet[m] B ∧ E =ᵐ[P] B := by
  constructor
  · exact exists_measurable_ae_eq_of_sup_nullSets
  · rintro ⟨B, hB, he⟩
    have hN : MeasurableSet[Filtration.nullSets P] (E ∆ B) :=
      MeasurableSpace.measurableSet_generateFrom (measure_symmDiff_eq_zero_iff.mpr he)
    have hB' : MeasurableSet[m ⊔ Filtration.nullSets P] B :=
      (le_sup_left : m ≤ m ⊔ Filtration.nullSets P) B hB
    have hN' : MeasurableSet[m ⊔ Filtration.nullSets P] (E ∆ B) :=
      (le_sup_right : Filtration.nullSets P ≤ m ⊔ Filtration.nullSets P) _ hN
    have hset : E = B ∆ (E ∆ B) := by
      ext ω
      simp only [mem_symmDiff]
      tauto
    rw [hset]
    exact hB'.symmDiff hN'

end ProbabilityTheory

namespace MeasureTheory.Filtration

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
  {F : Filtration ℝ≥0 mΩ}

/-- Null-set enlargement on the completed space preserves right continuity
of the original nonnegative-real-time filtration. -/
theorem IsRightContinuous.withNullSets (hF : F.IsRightContinuous) :
    (F.withNullSets P).IsRightContinuous := by
  classical
  constructor
  intro t E hE
  obtain ⟨u, hu, htu, hlim⟩ := exists_seq_strictAnti_tendsto t
  have hfuture (n : ℕ) : MeasurableSet[F.withNullSets P (u n)] E := by
    have hle : (F.withNullSets P).rightCont t ≤ F.withNullSets P (u n) := by
      rw [rightCont_eq]
      exact iInf₂_le (u n) (htu n)
    exact hle E hE
  have hrep (n : ℕ) : ∃ B : Set Ω, MeasurableSet[F (u n)] B ∧ E =ᵐ[P] B :=
    ProbabilityTheory.exists_measurable_ae_eq_of_sup_nullSets (hfuture n)
  choose B hmB heB using hrep
  let C : Set Ω := ⋂ n : ℕ, ⋃ k : ℕ, B (n + k)
  have heC : E =ᵐ[P] C := by
    filter_upwards [ae_all_iff.mpr heB] with ω hω
    change (ω ∈ E) = (ω ∈ C)
    apply propext
    simp only [C, mem_iInter]
    constructor
    · intro he n
      exact mem_iUnion.mpr ⟨0, Eq.mp (hω (n + 0)) he⟩
    · intro hc
      obtain ⟨k, hk⟩ := mem_iUnion.mp (hc 0)
      exact Eq.mpr (hω (0 + k)) hk
  have hmC : MeasurableSet[F.rightCont t] C := by
    rw [rightCont_eq]
    apply MeasurableSpace.measurableSet_iInf.mpr
    intro v
    apply MeasurableSpace.measurableSet_iInf.mpr
    intro htv
    obtain ⟨N, hN⟩ := (hlim.eventually (Iio_mem_nhds htv)).exists
    have htail : C = ⋂ n : ℕ, ⋃ k : ℕ, B (N + n + k) := by
      ext ω
      simp only [C, mem_iInter, mem_iUnion]
      constructor
      · intro hc n
        exact hc (N + n)
      · intro hc n
        obtain ⟨k, hk⟩ := hc n
        refine ⟨N + k, ?_⟩
        simpa only [show n + (N + k) = N + n + k by omega] using hk
    rw [htail]
    apply MeasurableSet.iInter
    intro n
    apply MeasurableSet.iUnion
    intro k
    exact F.mono ((hu.antitone (by omega : N ≤ N + n + k)).trans hN.le)
      _ (hmB (N + n + k))
  have hmCt : MeasurableSet[F t] C := hF.RC t C hmC
  change MeasurableSet[F t ⊔ nullSets P] E
  exact (ProbabilityTheory.measurableSet_sup_nullSets_iff (P := P)).mpr ⟨C, hmCt, heC⟩

/-- For an already right-continuous raw filtration, usual augmentation
adds null sets but no further right-continuation information. -/
theorem usualAugmentation_eq_withNullSets (hF : F.IsRightContinuous) :
    F.usualAugmentation P = F.withNullSets P := by
  let := hF.withNullSets (P := P)
  exact IsRightContinuous.eq

end MeasureTheory.Filtration
