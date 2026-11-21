/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import Mathlib.Probability.Martingale.OptionalSampling

/-! # One-sided terminal bounds at countable-range stopping times

The native stopping sigma-field agrees with a deterministic sigma-field on
each stopping-time fiber. Its existing conditional-expectation restriction
lemma transports the one-sided inequality. Countability, not an uncountable
intersection of coordinate events, permits assembling these comparisons.
These bounds alone do not assert integrability of the stopped variable.
-/

@[expose] public section

open Filter Set
open scoped NNReal ENNReal

namespace MeasureTheory

variable {Ω ι : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsFiniteMeasure P]
  [LinearOrder ι] [TopologicalSpace ι] [OrderTopology ι] [FirstCountableTopology ι]
  [Nonempty ι] {F : Filtration ι mΩ} {X : ι → Ω → ℝ} {τ : Ω → WithTop ι} {T : ι}

theorem Submartingale.stoppedValue_ae_le_condExp_of_le_const_of_countable_range
    (hX : Submartingale X F P) (hτ : IsStoppingTime F τ) (hb : ∀ ω, τ ω ≤ T)
    (hc : (Set.range τ).Countable) : stoppedValue X τ ≤ᵐ[P] P[X T | hτ.measurableSpace] := by
  have hu : Set.univ = ⋃ i ∈ Set.range τ, {ω | τ ω = i} := by
    ext ω
    simp only [Set.mem_univ, Set.mem_range, Set.iUnion_exists, Set.iUnion_iUnion_eq',
      Set.mem_iUnion, Set.mem_ofPred_eq, exists_apply_eq_apply']
  suffices h : ∀ᵐ ω ∂P.restrict (⋃ i ∈ Set.range τ, {ω | τ ω = i}),
      stoppedValue X τ ω ≤ P[X T | hτ.measurableSpace] ω by
    simpa only [Filter.EventuallyLE, ← hu, Measure.restrict_univ] using h
  rw [ae_restrict_biUnion_iff _ hc]
  intro i hi
  have hn : i ≠ ⊤ := by
    obtain ⟨ω, rfl⟩ := hi
    exact ne_top_of_le_ne_top (by simp) (hb ω)
  lift i to ι using hn with i
  have hiT : i ≤ T := by
    obtain ⟨ω, hω⟩ := hi
    exact WithTop.coe_le_coe.mp (hω ▸ hb ω)
  have hce : P[X T | hτ.measurableSpace] =ᵐ[P.restrict {ω | τ ω = i}] P[X T | F i] := by
    apply condExp_ae_eq_restrict_of_measurableSpace_eq_on
      hτ.measurableSpace_le (F.le i) (hτ.measurableSet_eq' i)
    intro A
    rw [Set.inter_comm _ A, IsStoppingTime.measurableSet_inter_eq_iff]
  have hs : stoppedValue X τ =ᵐ[P.restrict {ω | τ ω = i}] X i := by
    rw [Filter.EventuallyEq, ae_restrict_iff' (F.le i _ (hτ.measurableSet_eq i))]
    apply Eventually.of_forall
    intro ω hω
    change τ ω = (i : WithTop ι) at hω
    simp only [stoppedValue, hω, WithTop.untopA, WithTop.untopD_coe]
  filter_upwards [hs, hce, ae_restrict_of_ae (hX.ae_le_condExp hiT)] with ω hsω heω hXω
  simpa only [hsω, heω] using hXω

theorem Supermartingale.condExp_ae_le_stoppedValue_of_le_const_of_countable_range
    (hX : Supermartingale X F P) (hτ : IsStoppingTime F τ) (hb : ∀ ω, τ ω ≤ T)
    (hc : (Set.range τ).Countable) : P[X T | hτ.measurableSpace] ≤ᵐ[P] stoppedValue X τ := by
  have h := hX.neg.stoppedValue_ae_le_condExp_of_le_const_of_countable_range hτ hb hc
  filter_upwards [h, condExp_neg (X T) hτ.measurableSpace] with ω hω heω
  simpa only [stoppedValue_neg, Pi.neg_apply, heω, neg_le_neg_iff] using hω

end MeasureTheory
