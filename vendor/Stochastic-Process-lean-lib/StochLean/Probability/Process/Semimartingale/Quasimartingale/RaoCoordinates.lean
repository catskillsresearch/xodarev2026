/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.Semimartingale.Quasimartingale.FutureEnvelopeBalance
public import
  StochLean.Probability.Process.Semimartingale.Quasimartingale.FutureEnvelopeSupermartingale

/-! # Actual nonnegative supermartingale coordinates

The already constructed positive and negative whole-future partition envelopes
give genuine supermartingale coordinates with uniform first-moment bounds.
The balance identity holds separately at each time. No path regularization or
cadlag Rao decomposition is claimed here, and no second envelope selector is
introduced. Right-continuous expectations of either coordinate are not assumed.
-/

@[expose] public section

open MeasureTheory StochLean Finset Filter
open scoped NNReal ENNReal

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsFiniteMeasure P]
  {F : Filtration ℝ≥0 mΩ} {X : ℝ≥0 → Ω → ℝ}

/-- Finite actual conditional variation constructs two nonnegative
supermartingale coordinates, before any cadlag regularization. -/
theorem exists_nonnegative_supermartingale_coordinates_of_finiteConditionalVariation
    (ha : Adapted F X) (hi : ∀ t, Integrable (X t) P)
    (hv : HasFiniteConditionalVariation X F P) :
    ∃ U V : ℝ≥0 → Ω → ℝ,
      Supermartingale U F P ∧ Supermartingale V F P ∧
      (∀ t ω, 0 ≤ U t ω ∧ 0 ≤ V t ω) ∧ (∀ t, U t - V t =ᵐ[P] X t) ∧
      (∀ t, (∫ ω, U t ω ∂P) ≤ (eConditionalVariation X F P).toReal) ∧
      (∀ t, (∫ ω, V t ω ∂P) ≤ (eConditionalVariation X F P).toReal) := by
  classical
  choose Wp Wn hmp hmn hp hn hbp hbn hfin using
    exists_future_positive_negative_partitionEnvelopes ha hi
  let U : ℝ≥0 → Ω → ℝ := fun t ω ↦ (Wp t ω).toReal
  let V : ℝ≥0 → Ω → ℝ := fun t ω ↦ (Wn t ω).toReal
  have hU : Supermartingale U F P := by
    apply supermartingale_future_positive_partitionEnvelopes ha hi hv hmp
    intro t
    simpa only [Filtration.reindex_apply, add_zero] using hp t
  have hvneg : HasFiniteConditionalVariation (-X) F P := by
    unfold HasFiniteConditionalVariation
    rw [eConditionalVariation_neg_eq]
    exact hv
  have hV : Supermartingale V F P := by
    apply supermartingale_future_positive_partitionEnvelopes (X := -X) ha.neg
      (fun t ↦ (hi t).neg) hvneg hmn
    intro t
    simpa only [Filtration.reindex_apply, add_zero, Pi.neg_apply] using hn t
  refine ⟨U, V, hU, hV, fun _ _ ↦ ⟨ENNReal.toReal_nonneg, ENNReal.toReal_nonneg⟩,
    fun t ↦ future_partitionEnvelopes_sub_ae_eq ha hi hv t (hp t) (hn t), ?_, ?_⟩
  · intro t
    have hff := (hfin t hv).1.mono fun _ hω ↦ hω.1.lt_top
    rw [show (∫ ω, U t ω ∂P) = (∫⁻ ω, Wp t ω ∂P).toReal from
      integral_toReal (hp t).measurable.aemeasurable hff]
    exact ENNReal.toReal_mono hv (hbp t)
  · intro t
    have hff := (hfin t hv).1.mono fun _ hω ↦ hω.2.lt_top
    rw [show (∫ ω, V t ω ∂P) = (∫⁻ ω, Wn t ω ∂P).toReal from
      integral_toReal (hn t).measurable.aemeasurable hff]
    exact ENNReal.toReal_mono hv (hbn t)

end ProbabilityTheory
