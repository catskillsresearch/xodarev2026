/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.Counting.ArrivalConstruction

/-! # Natural count information before the next indexed arrival

On the event that arrival `n` has not occurred by `t`, every count observed
up to `t` is determined by the first `n` actual arrival coordinates. A raw
natural-filtration event therefore has the same restriction to this event
as a measurable event in that finite arrival history.

The proof uses the existing guarded count and its exact closed-arrival
characterization. On the survival subtype, count upper rays of index below
`n` are measurable history-coordinate events; all higher upper rays are
empty. Native natural-filtration and comap constructions then give the
event representation. No probability, conditional expectation, new history
filtration, or alternative count selector is involved. The case `n = 0`
retains its genuinely empty history.
-/

@[expose] public section

open MeasureTheory Set
open scoped NNReal

namespace ProbabilityTheory.IsNonexplosiveArrivalSequence

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {Γ : ℕ → Ω → WithTop ℝ≥0}

/-- Before indexed arrival `n`, a raw natural-count event is the restriction
of a measurable event in the first `n` actual arrival coordinates. -/
theorem measurableSet_natural_count_on_survival
    (hΓ : ∀ ω, IsNonexplosiveArrivalSequence (fun k ↦ Γ k ω))
    (hMeas : ∀ k, Measurable (Γ k)) (t : ℝ≥0) (n : ℕ) {E : Set Ω}
    (hE : MeasurableSet[(Filtration.natural
      (fun s ω ↦ (hΓ ω).count s)
      (fun s ↦ (measurable_count hΓ hMeas s).stronglyMeasurable)) t] E) :
    ∃ B : Set (Fin n → WithTop ℝ≥0), MeasurableSet B ∧
      E ∩ {ω | (t : WithTop ℝ≥0) < Γ n ω} =
        (fun ω (i : Fin n) ↦ Γ i ω) ⁻¹' B ∩ {ω | (t : WithTop ℝ≥0) < Γ n ω} := by
  classical
  let N : ℝ≥0 → Ω → ℕ := fun s ω ↦ (hΓ ω).count s
  let hN : ∀ s, StronglyMeasurable (N s) :=
    fun s ↦ (measurable_count hΓ hMeas s).stronglyMeasurable
  let F := Filtration.natural N hN
  let S : Set Ω := {ω | (t : WithTop ℝ≥0) < Γ n ω}
  let H : S → Fin n → WithTop ℝ≥0 := fun ω i ↦ Γ i ω
  let mH : MeasurableSpace S := MeasurableSpace.comap H inferInstance
  let : MeasurableSpace S := mH
  have hH : Measurable H := measurable_iff_comap_le.mpr le_rfl
  have hcount (s : ℝ≥0) (hst : s ≤ t) : Measurable (fun ω : S ↦ N s ω) := by
    apply measurable_of_Ioi
    intro k
    by_cases hkn : k < n
    · have he : (fun ω : S ↦ N s ω) ⁻¹' Ioi k =
          {ω : S | H ω ⟨k, hkn⟩ ≤ (s : WithTop ℝ≥0)} := by
        ext ω
        exact (hΓ ω).lt_count_iff s k
      rw [he]
      exact measurableSet_le (hH.eval (a := (⟨k, hkn⟩ : Fin n))) measurable_const
    · have he : (fun ω : S ↦ N s ω) ⁻¹' Ioi k = ∅ := by
        apply eq_empty_iff_forall_notMem.mpr
        intro ω hk
        change k < (hΓ ω).count s at hk
        have hn : (hΓ ω).count s ≤ n :=
          ((hΓ ω).count_le_iff s n).mpr
            ((WithTop.coe_le_coe.mpr hst).trans_lt ω.property)
        exact (not_lt_of_ge (hn.trans (le_of_not_gt hkn))) hk
      rw [he]
      exact MeasurableSet.empty
  have hfield : MeasurableSpace.comap (Subtype.val : S → Ω) (F t) ≤ mH := by
    change MeasurableSpace.comap (Subtype.val : S → Ω)
      ((Filtration.natural N hN) t) ≤ mH
    rw [Filtration.natural_eq_comap, MeasurableSpace.comap_comp]
    exact (measurable_pi_lambda (fun ω : S ↦ fun s : Iic t ↦ N s ω)
      (fun s ↦ hcount s s.property)).comap_le
  have hES : MeasurableSet[mH] ((Subtype.val : S → Ω) ⁻¹' E) :=
    hfield _ (MeasurableSpace.measurableSet_comap.mpr ⟨E, hE, rfl⟩)
  obtain ⟨B, hB, hBE⟩ := MeasurableSpace.measurableSet_comap.mp hES
  refine ⟨B, hB, ?_⟩
  change E ∩ S = (fun ω (i : Fin n) ↦ Γ i ω) ⁻¹' B ∩ S
  ext ω
  by_cases hω : ω ∈ S
  · have hh := Set.ext_iff.mp hBE (⟨ω, hω⟩ : S)
    change (fun i : Fin n ↦ Γ i ω) ∈ B ↔ ω ∈ E at hh
    simpa only [mem_inter_iff, mem_preimage, hω, and_true] using hh.symm
  · simp only [mem_inter_iff, mem_preimage, hω, and_false]

end ProbabilityTheory.IsNonexplosiveArrivalSequence
