/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.FiniteVariation.PredictableJumps
public import StochLean.Probability.Process.Stopping.PredictableDisjointGraphs

/-! # Disjoint positive predictable coverage of actual FV jumps

The already constructed predictable jump cover is made disjoint by legitimate
before-field restrictions. Positive finite jump points are retained exactly.
All resulting lifetimes are strictly positive, and infinite times carry no
finite graph point. The common almost-sure cover concerns the original process.
-/

@[expose] public section

open ProbabilityTheory MeasureTheory Set
open scoped NNReal

namespace MeasureTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {F : Filtration ℝ≥0 mΩ}
  {P : Measure Ω} [IsProbabilityMeasure P] {X : ℝ≥0 → Ω → ℝ}

/-- Every positive FV jump is covered, without repetition on any finite
graph. Neither a covering sequence nor a graph section theorem is an input. -/
theorem IsStronglyPredictable.exists_positive_disjoint_predictableStoppingTime_cover_jumps
    (hX : IsStronglyPredictable F X) (hF : F.IsUsual P)
    (hc : HasCadlagPaths X P) (hv : HasFiniteVariationPaths X P) :
    ∃ ρ : ℕ → Ω → WithTop ℝ≥0,
      (∀ n, IsPredictableStoppingTime F (ρ n) P) ∧
        (∀ n ω, 0 < ρ n ω) ∧
          Pairwise (fun n m ↦ Disjoint (stoppingTimeGraph (ρ n)) (stoppingTimeGraph (ρ m))) ∧
            ∀ᵐ ω ∂P, ∀ t : ℝ≥0, 0 < t → jumpProcess X t ω ≠ 0 →
              ∃ n, ρ n ω = (t : WithTop ℝ≥0) := by
  obtain ⟨σ, hσ, hcover⟩ := hX.exists_predictableStoppingTime_cover_jumps hF hc hv
  obtain ⟨ρ, hρ, hp, _, hd, hu⟩ :=
    exists_positive_predictableStoppingTime_disjoint_graph_restrictions σ hσ hF
  refine ⟨ρ, hρ, hp, hd, ?_⟩
  filter_upwards [hcover] with ω hω t ht hj
  obtain ⟨n, hn⟩ := hω t ht hj
  have hm : (t, ω) ∈ ⋃ k, stoppingTimeGraph (ρ k) := by
    rw [hu]
    exact ⟨⟨ht, mem_univ ω⟩, mem_iUnion.mpr ⟨n, hn⟩⟩
  obtain ⟨k, hk⟩ := mem_iUnion.mp hm
  exact ⟨k, hk⟩

end MeasureTheory
