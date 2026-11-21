/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.Measurability.PredictableGenerators
public import Mathlib.MeasureTheory.Measure.Trim
public import Mathlib.MeasureTheory.Measure.Typeclasses.Finite

/-! # Finite-measure uniqueness on the predictable sigma-field

Agreement on the actual native predictable generators determines the trims
of two finite ambient product measures. The initial singleton is retained.
An equivalent consumer uses finite time rectangles and derives the infinite
future rectangles by increasing unions. No predictable sigma-field or
stochastic measure is redefined, and no stochastic integral is assumed.
-/

@[expose] public section

open Set
open scoped NNReal

namespace MeasureTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

/-- Every native predictable generator is ambient product measurable. -/
theorem Filtration.predictable_le_prod (F : Filtration ℝ≥0 mΩ) :
    F.predictable ≤ (inferInstance : MeasurableSpace ℝ≥0).prod mΩ := by
  apply measurableSpace_le_predictable_of_measurableSet
  · intro A hA
    exact (measurableSet_singleton _).prod (F.le _ A hA)
  · intro t A hA
    exact measurableSet_Ioi.prod (F.le t A hA)

private theorem isPiSystem_predictable_generators (F : Filtration ℝ≥0 mΩ) :
    IsPiSystem ({s | ∃ A, MeasurableSet[F 0] A ∧ s = {0} ×ˢ A} ∪
      {s | ∃ t A, MeasurableSet[F t] A ∧ s = Ioi t ×ˢ A}) := by
  rintro _ (⟨A, hA, rfl⟩ | ⟨s, A, hA, rfl⟩)
    _ (⟨B, hB, rfl⟩ | ⟨t, B, hB, rfl⟩) hne
  · left
    refine ⟨A ∩ B, hA.inter hB, ?_⟩
    rw [prod_inter_prod, inter_self]
  · obtain ⟨⟨u, ω⟩, hu, hv⟩ := hne
    have hz : u = 0 := hu.1
    have ht : t < u := hv.1
    rw [hz] at ht
    exact (not_lt_of_ge (show (0 : ℝ≥0) ≤ t from zero_le) ht).elim
  · obtain ⟨⟨u, ω⟩, hu, hv⟩ := hne
    have hz : u = 0 := hv.1
    have hs : s < u := hu.1
    rw [hz] at hs
    exact (not_lt_of_ge (show (0 : ℝ≥0) ≤ s from zero_le) hs).elim
  · right
    refine ⟨max s t, A ∩ B,
      (F.mono (le_max_left s t) A hA).inter (F.mono (le_max_right s t) B hB), ?_⟩
    rw [prod_inter_prod, Ioi_inter_Ioi]

namespace Measure

variable (F : Filtration ℝ≥0 mΩ) {μ ν : Measure (ℝ≥0 × Ω)}
  [IsFiniteMeasure μ]

/-- Equality on the exact initial and strict-future generators gives
equality of the two restrictions to the existing predictable sigma-field. -/
theorem trim_predictable_eq_of_Ioi
    (h0 : ∀ A, MeasurableSet[F 0] A → μ ({0} ×ˢ A) = ν ({0} ×ˢ A))
    (hIoi : ∀ t A, MeasurableSet[F t] A → μ (Ioi t ×ˢ A) = ν (Ioi t ×ˢ A)) :
    μ.trim F.predictable_le_prod = ν.trim F.predictable_le_prod := by
  have hu : ({0} ×ˢ (univ : Set Ω)) ∪ (Ioi (0 : ℝ≥0) ×ˢ univ) = univ := by
    ext ⟨t, ω⟩
    simp only [mem_union, mem_prod, mem_singleton_iff, mem_univ, and_true, mem_Ioi,
      iff_true]
    rcases eq_or_lt_of_le (bot_le : (0 : ℝ≥0) ≤ t) with h | h
    · exact Or.inl h.symm
    · exact Or.inr h
  have hd : Disjoint ({0} ×ˢ (univ : Set Ω)) (Ioi (0 : ℝ≥0) ×ˢ univ) := by
    apply disjoint_left.mpr
    intro p hp hq
    have hz : p.1 = 0 := hp.1
    exact (lt_irrefl (0 : ℝ≥0)) (hz ▸ hq.1)
  have hm : MeasurableSet (Ioi (0 : ℝ≥0) ×ˢ (univ : Set Ω)) :=
    measurableSet_Ioi.prod MeasurableSet.univ
  have hmass : μ univ = ν univ := by
    calc
      μ univ = μ ({0} ×ˢ univ) + μ (Ioi 0 ×ˢ univ) :=
        (congrArg μ hu).symm.trans (measure_union hd hm)
      _ = ν ({0} ×ˢ univ) + ν (Ioi 0 ×ˢ univ) := by
        rw [h0 univ MeasurableSet.univ, hIoi 0 univ MeasurableSet.univ]
      _ = ν univ := (measure_union hd hm).symm.trans (congrArg ν hu)
  apply @Measure.ext (ℝ≥0 × Ω) F.predictable
  intro E hE
  rw [trim_measurableSet_eq _ hE, trim_measurableSet_eq _ hE]
  apply ext_on_measurableSpace_of_generate_finite
    ((inferInstance : MeasurableSpace ℝ≥0).prod mΩ)
    ({s | ∃ A, MeasurableSet[F 0] A ∧ s = {0} ×ˢ A} ∪
      {s | ∃ t A, MeasurableSet[F t] A ∧ s = Ioi t ×ˢ A})
    ?_ F.predictable_le_prod rfl (isPiSystem_predictable_generators F) hmass hE
  rintro _ (⟨A, hA, rfl⟩ | ⟨t, A, hA, rfl⟩)
  · exact h0 A hA
  · exact hIoi t A hA

/-- Finite time rectangles suffice. Their increasing integer-horizon union
recovers every strict-future generator, while the zero-time atom is explicit. -/
theorem trim_predictable_eq_of_Ioc
    (h0 : ∀ A, MeasurableSet[F 0] A → μ ({0} ×ˢ A) = ν ({0} ×ˢ A))
    (hIoc : ∀ s t A, MeasurableSet[F s] A → μ (Ioc s t ×ˢ A) = ν (Ioc s t ×ˢ A)) :
    μ.trim F.predictable_le_prod = ν.trim F.predictable_le_prod := by
  apply trim_predictable_eq_of_Ioi F h0
  intro s A hA
  have he : (⋃ n : ℕ, Ioc s (n : ℝ≥0) ×ˢ A) = Ioi s ×ˢ A := by
    ext p
    simp only [mem_iUnion, mem_prod, mem_Ioc, mem_Ioi]
    constructor
    · rintro ⟨n, ⟨hlo, _⟩, hp⟩
      exact ⟨hlo, hp⟩
    · rintro ⟨hlo, hp⟩
      obtain ⟨n, hn⟩ := exists_nat_ge p.1
      exact ⟨n, ⟨hlo, hn⟩, hp⟩
  have hmono : Monotone (fun n : ℕ ↦ Ioc s (n : ℝ≥0) ×ˢ A) := by
    intro n m hnm p hp
    exact ⟨⟨hp.1.1, hp.1.2.trans (by exact_mod_cast hnm)⟩, hp.2⟩
  rw [← he, hmono.measure_iUnion, hmono.measure_iUnion]
  exact iSup_congr fun n ↦ hIoc s (n : ℝ≥0) A hA

end Measure

end MeasureTheory
