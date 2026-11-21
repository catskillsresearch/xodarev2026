/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.Counting.SingleJumpInformation

/-! # Capping a lifetime loses its observation-endpoint event

On a two-point space the lifetime is either one or two. Capping it at one
is constant, so it generates the trivial sigma field. The original closed
single-jump count at one still distinguishes the two points. This is actual
nonmeasurability, not just inequality between two chosen representations.
No measure or null-event argument is involved in this raw information test.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set
open scoped NNReal

namespace StochLean.SemimartingaleRegression

/-- The raw natural information of a closed count cannot be replaced by
the information of the capped lifetime when the endpoint can be attained. -/
theorem singleJumpCount_endpoint_not_measurable_from_capped_lifetime :
    let τ : Bool → WithTop ℝ≥0 := fun b ↦ if b then 1 else 2
    let N : ℝ≥0 → Bool → ℕ := fun t b ↦ if τ b ≤ (t : WithTop ℝ≥0) then 1 else 0
    let hτ : Measurable τ := measurable_of_countable τ
    let F := Filtration.natural N (stronglyMeasurable_singleJumpCount hτ)
    Measurable[F 1] (N 1) ∧
      ¬ Measurable[MeasurableSpace.comap
        (fun b ↦ min (τ b) (1 : WithTop ℝ≥0)) inferInstance] (N 1) := by
  intro τ N hτ F
  have ha : StronglyAdapted F N :=
    Filtration.stronglyAdapted_natural (stronglyMeasurable_singleJumpCount hτ)
  refine ⟨(ha 1).measurable, ?_⟩
  have he : (fun b ↦ min (τ b) (1 : WithTop ℝ≥0)) = fun _ : Bool ↦ 1 := by
    funext b
    cases b <;> norm_num [τ]
  rw [he, MeasurableSpace.comap_const]
  intro hm
  have hmE : MeasurableSet[⊥] ((N 1) ⁻¹' {1}) := hm (measurableSet_singleton 1)
  have ht : true ∈ (N 1) ⁻¹' {1} := by
    change (if (1 : WithTop ℝ≥0) ≤ 1 then (1 : ℕ) else 0) = 1
    rw [if_pos le_rfl]
  have hf : false ∉ (N 1) ⁻¹' {1} := by
    change ¬ (if (2 : WithTop ℝ≥0) ≤ 1 then (1 : ℕ) else 0) = 1
    rw [if_neg (by norm_num : ¬ (2 : WithTop ℝ≥0) ≤ 1)]
    exact Nat.zero_ne_one
  rcases MeasurableSpace.measurableSet_bot_iff.mp hmE with hE | hE
  · rw [hE] at ht
    exact ht
  · apply hf
    rw [hE]
    exact mem_univ _

end StochLean.SemimartingaleRegression
