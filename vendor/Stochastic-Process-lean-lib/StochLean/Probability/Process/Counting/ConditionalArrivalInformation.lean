/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.Counting.ArrivalHistoryEquivalence
public import StochLean.ForMathlib.Probability.Kernel.CondDistribInformation

/-! # The actual conditional gap law is independent of history coordinates

The next actual interarrival duration may be conditioned on either the
preceding arrival coordinates or the preceding actual gap coordinates.
These generate exactly the same information on an everywhere-valid arrival
sequence. Native conditional distributions evaluated at the original
history therefore agree as measures on one common almost-sure event.

This compares the actual evaluated kernels, not arbitrary history labels.
It does not conflate absorbing actual gaps with independent latent gaps,
and it requires no standard Borel assumption on the original sample space.
The zero-length history and infinite arrival tails are retained.
-/

@[expose] public section

open MeasureTheory
open scoped NNReal ENNReal

namespace ProbabilityTheory.IsNonexplosiveArrivalSequence

/-- The next actual gap has the same native conditional law given actual
arrival history or actual gap history, as measures on one common event. -/
theorem condDistrib_arrivalInterarrival_history_ae_eq
    {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsFiniteMeasure P]
    {Γ : ℕ → Ω → WithTop ℝ≥0}
    (hΓ : ∀ ω, IsNonexplosiveArrivalSequence (fun k ↦ Γ k ω))
    (hMeas : ∀ k, Measurable (Γ k)) (n : ℕ) :
    let : StandardBorelSpace (WithTop ℝ≥0) := inferInstanceAs (StandardBorelSpace ℝ≥0∞)
    let S := fun ω ↦ arrivalInterarrival (fun k ↦ Γ k ω) n
    let A := fun ω (i : Fin n) ↦ Γ i ω
    let G := fun ω (i : Fin n) ↦ arrivalInterarrival (fun k ↦ Γ k ω) i
    (fun ω ↦ condDistrib S A P (A ω)) =ᵐ[P] fun ω ↦ condDistrib S G P (G ω) := by
  let : StandardBorelSpace (WithTop ℝ≥0) := inferInstanceAs (StandardBorelSpace ℝ≥0∞)
  exact condDistrib_comp_ae_eq_of_comap_eq
    (measurable_pi_lambda _ fun i : Fin n ↦ hMeas i)
    (measurable_pi_lambda _ fun i : Fin n ↦ measurable_arrivalInterarrival hMeas i)
    (measurable_arrivalInterarrival hMeas n)
    (comap_arrival_history_eq_interarrival_history hΓ n)

end ProbabilityTheory.IsNonexplosiveArrivalSequence
