/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Independence.Completion

/-! # Jointly independent families under genuine measure completion

Completing the original ambient measure preserves the full independence
of an arbitrary indexed family, including dependent target spaces. The
finite-family preimage-intersection identity is transported unchanged:
the completed measure has the original outer measure on all original
sets. No reduction to pairwise independence, countability of the index,
or finiteness of the measure is used.
-/

@[expose] public section

open MeasureTheory Set

namespace ProbabilityTheory

/-- A genuinely jointly independent family remains jointly independent
on the completed ambient space, for any index and dependent state
spaces. The measure need not be finite or a probability measure. -/
theorem iIndepFun.completion
    {ι : Type*} {β : ι → Type*} {mβ : ∀ i, MeasurableSpace (β i)}
    {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
    {f : ∀ i, Ω → β i} (hi : iIndepFun f P) :
    iIndepFun (fun i (ω : NullMeasurableSpace Ω P) ↦ f i ω) P.completion := by
  apply iIndepFun_iff_measure_inter_preimage_eq_mul.mpr
  intro S sets hsets
  change P (⋂ i ∈ S, f i ⁻¹' sets i) = ∏ i ∈ S, P (f i ⁻¹' sets i)
  exact hi.measure_inter_preimage_eq_mul S hsets

end ProbabilityTheory
