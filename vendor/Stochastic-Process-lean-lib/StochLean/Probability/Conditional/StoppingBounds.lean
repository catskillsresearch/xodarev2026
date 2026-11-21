/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import Mathlib.Probability.Process.Stopping

/-! # Conditional bounds sampled on countable-range stopping times

A coordinatewise conditional bound can be assembled on countably many
stopping fibers. No martingale, integrability of the stopped process, or
continuity hypothesis is smuggled into this purely conditional step.
-/

@[expose] public section

open Filter Set

namespace MeasureTheory

variable {Ω ι : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsFiniteMeasure P]
  [LinearOrder ι] [TopologicalSpace ι] [OrderTopology ι] [FirstCountableTopology ι]
  [Nonempty ι] {F : Filtration ι mΩ} {X : ι → Ω → ℝ} {Y : Ω → ℝ}
  {τ : Ω → WithTop ι}

theorem condExp_le_stoppedValue_of_countable_range
    (hclose : ∀ t, P[Y | F t] ≤ᵐ[P] X t) (hτ : IsStoppingTime F τ)
    (hf : ∀ ω, τ ω ≠ ⊤) (hc : (Set.range τ).Countable) :
    P[Y | hτ.measurableSpace] ≤ᵐ[P] stoppedValue X τ := by
  have hu : Set.univ = ⋃ i ∈ Set.range τ, {ω | τ ω = i} := by
    ext ω
    simp only [Set.mem_univ, Set.mem_range, Set.iUnion_exists, Set.iUnion_iUnion_eq',
      Set.mem_iUnion, Set.mem_ofPred_eq, exists_apply_eq_apply']
  suffices h : ∀ᵐ ω ∂P.restrict (⋃ i ∈ Set.range τ, {ω | τ ω = i}),
      P[Y | hτ.measurableSpace] ω ≤ stoppedValue X τ ω by
    simpa only [Filter.EventuallyLE, ← hu, Measure.restrict_univ] using h
  rw [ae_restrict_biUnion_iff _ hc]
  intro i hi
  have hn : i ≠ ⊤ := by
    obtain ⟨ω, rfl⟩ := hi
    exact hf ω
  lift i to ι using hn with i
  have hce : P[Y | hτ.measurableSpace] =ᵐ[P.restrict {ω | τ ω = i}] P[Y | F i] := by
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
  filter_upwards [hs, hce, ae_restrict_of_ae (hclose i)] with ω hsω heω hXω
  simpa only [hsω, heω] using hXω

end MeasureTheory
