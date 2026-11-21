/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.Stopping.PartitionIndex

/-! # Stopping information under finite-partition indexing

Ceiling approximation cannot lose information already available at the
original stopping time. These comparisons use only the native stopping
sigma-fields, including their terminal-field measurability requirement.
On-grid times have exactly the same stopping information as their indices.
-/

@[expose] public section

open StochLean MeasureTheory Set
open scoped NNReal

namespace ProbabilityTheory.FiniteStoppingTime

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {F : Filtration ℝ≥0 mΩ} {T : ℝ≥0}

theorem measurableSpace_le_ceilingIndex (τ : FiniteStoppingTime F) (π : TimePartition T)
    (hb : ∀ ω, τ ω ≤ T) :
    τ.measurableSpace ≤ (τ.isStoppingTime_ceilingIndex π hb).measurableSpace := by
  have ht : π.pointNat π.size = T := by
    simpa only [Fin.val_last] using
      (π.pointNat_fin (Fin.last π.size)).trans π.last_eq_horizon
  intro A hA
  have hAT : MeasurableSet[F T] A :=
    τ.isStoppingTime.measurableSpace_le_of_le_const
      (fun ω ↦ WithTop.coe_le_coe.mpr (hb ω)) A hA
  refine ⟨?_, fun k ↦ ?_⟩
  · apply le_iSup (F.reindex π.pointNat π.pointNat_mono) π.size A
    change MeasurableSet[F (π.pointNat π.size)] A
    rwa [ht]
  · change MeasurableSet[F (π.pointNat k)]
      (A ∩ {ω | ((π.ceilingIndex (τ ω)).val : WithTop ℕ) ≤ k})
    have h := hA.2 (π.pointNat k)
    convert h using 1
    ext ω
    simp only [Set.mem_inter_iff, Set.mem_ofPred_eq,
      ← WithTop.coe_natCast, Nat.cast_id, WithTop.coe_le_coe]
    rw [π.ceilingIndex_le_iff (hb ω) k]

/-- If the stopping time already takes partition values, ceiling indexing
preserves its entire native stopping sigma-field, even with repeated points. -/
theorem measurableSpace_ceilingIndex_eq (τ : FiniteStoppingTime F) (π : TimePartition T)
    (hb : ∀ ω, τ ω ≤ T) (hm : ∀ ω, τ ω ∈ Set.range π.point) :
    (τ.isStoppingTime_ceilingIndex π hb).measurableSpace = τ.measurableSpace := by
  apply le_antisymm ?_ (τ.measurableSpace_le_ceilingIndex π hb)
  let ξ : Ω → WithTop ℕ := fun ω ↦ (π.ceilingIndex (τ ω)).val
  have hξ : IsStoppingTime (F.reindex π.pointNat π.pointNat_mono) ξ :=
    τ.isStoppingTime_ceilingIndex π hb
  intro A hA
  have hterm : hξ.measurableSpace ≤ ⨆ t, F t :=
    hξ.measurableSpace_le'.trans (iSup_le fun k ↦ le_iSup F (π.pointNat k))
  refine ⟨hterm A hA, fun s ↦ ?_⟩
  have he : A ∩ {ω | (τ ω : WithTop ℝ≥0) ≤ s} =
      ⋃ (i : Fin (π.size + 1)) (_ : π.pointNat i.val ≤ s),
        A ∩ {ω | ξ ω = (i.val : WithTop ℕ)} := by
    ext ω
    simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, WithTop.coe_le_coe,
      Set.mem_iUnion, exists_prop]
    constructor
    · rintro ⟨hωA, hωs⟩
      refine ⟨π.ceilingIndex (τ ω), ?_, hωA, rfl⟩
      rwa [π.pointNat_ceilingIndex_eq_of_mem (hm ω)]
    · rintro ⟨i, his, hωA, hi⟩
      refine ⟨hωA, ?_⟩
      have hindex : (π.ceilingIndex (τ ω)).val = i.val := by
        dsimp only [ξ] at hi
        exact_mod_cast hi
      have ht : τ ω = π.pointNat i.val := by
        rw [← hindex, π.pointNat_ceilingIndex_eq_of_mem (hm ω)]
      exact ht.symm ▸ his
  rw [he]
  apply MeasurableSet.iUnion
  intro i
  apply MeasurableSet.iUnion
  intro his
  apply F.mono his
  apply (hξ.measurableSet_inter_eq_iff A i.val).mp
  exact hA.inter (hξ.measurableSet_eq' i.val)

end ProbabilityTheory.FiniteStoppingTime

namespace MeasureTheory.StronglyAdapted

open ProbabilityTheory

theorem stronglyMeasurable_partitionStoppingValue
    {Ω : Type*} {mΩ : MeasurableSpace Ω} {F : Filtration ℝ≥0 mΩ}
    {X : ℝ≥0 → Ω → ℝ} (hX : StronglyAdapted F X)
    (τ : FiniteStoppingTime F) {T : ℝ≥0} (π : TimePartition T)
    (hb : ∀ ω, τ ω ≤ T) (hm : ∀ ω, τ ω ∈ Set.range π.point) :
    StronglyMeasurable[τ.measurableSpace] (fun ω ↦ X (τ ω) ω) := by
  have ha : StronglyAdapted (F.reindex π.pointNat π.pointNat_mono)
      (fun k ↦ X (π.pointNat k)) := fun k ↦ hX _
  have h := (measurable_stoppedValue ha.isStronglyProgressive_of_discrete
    (τ.isStoppingTime_ceilingIndex π hb)).stronglyMeasurable
  rwa [τ.stoppedValue_ceilingIndex_eq X π hm, τ.measurableSpace_ceilingIndex_eq π hb hm] at h

end MeasureTheory.StronglyAdapted
