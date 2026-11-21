/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Analysis.PathVariation.StrictPartition
public import StochLean.Probability.Process.Semimartingale.Quasimartingale

/-! # Strict source partitions for conditional variation

Removing repeated endpoints preserves the actual conditional-variation sum, not
merely its expectation or an almost-everywhere version. Its terminal-zero tail is
unchanged because the finite horizon remains the same. Consequently the canonical
whole-half-line conditional variation is exactly the supremum over the strict
finite partitions in Protter III.4, followed by the artificial zero terminal value.
At horizon zero the representative is the singleton endpoint partition `{0}`;
the artificial final interval still contributes `|X 0|`.
-/

@[expose] public section

open MeasureTheory StochLean
open scoped NNReal ENNReal

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {X : ℝ≥0 → Ω → ℝ}
  {F : Filtration ℝ≥0 mΩ} {P : Measure Ω} {T : ℝ≥0}

/-- Repeated endpoints do not affect the actual conditional-variation random variable. -/
theorem conditionalVariationSum_eq_of_range_eq {π ρ : TimePartition T}
    (he : Set.range π.point = Set.range ρ.point) :
    conditionalVariationSum X F P π = conditionalVariationSum X F P ρ := by
  funext ω
  change (∑ i, |P[X (π.left i) - X (π.right i) | F (π.left i)] ω|) + |X T ω - 0| =
    (∑ i, |P[X (ρ.left i) - X (ρ.right i) | F (ρ.left i)] ω|) + |X T ω - 0|
  congr 1
  exact TimePartition.sum_cells_eq_of_range_eq he
    (fun s t ↦ |P[X s - X t | F s] ω|) (fun t ↦ by simp)

theorem eConditionalVariationOnPartition_eq_of_range_eq {π ρ : TimePartition T}
    (he : Set.range π.point = Set.range ρ.point) :
    eConditionalVariationOnPartition X F P π = eConditionalVariationOnPartition X F P ρ := by
  unfold eConditionalVariationOnPartition
  rw [conditionalVariationSum_eq_of_range_eq he]

/-- The canonical supremum equals the strict-source-partition supremum.
No second variation definition and no evaluation at infinite time is needed. -/
theorem eConditionalVariation_eq_iSup_strictMono :
    eConditionalVariation X F P =
      ⨆ T : ℝ≥0, ⨆ π : TimePartition T, ⨆ (_ : StrictMono π.point),
        eConditionalVariationOnPartition X F P π := by
  apply le_antisymm
  · apply iSup_le
    intro T
    apply iSup_le
    intro π
    obtain ⟨ρ, hρ, he⟩ := π.exists_strictMono_range_eq
    rw [eConditionalVariationOnPartition_eq_of_range_eq he.symm]
    exact le_iSup_of_le T (le_iSup_of_le ρ (le_iSup_of_le hρ le_rfl))
  · exact iSup_le fun T ↦ iSup_le fun π ↦ iSup_le fun _ ↦
      eConditionalVariationOnPartition_le π

end ProbabilityTheory
