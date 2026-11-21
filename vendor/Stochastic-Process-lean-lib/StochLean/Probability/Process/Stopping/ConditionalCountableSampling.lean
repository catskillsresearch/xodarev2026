/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Conditional.Locality
public import StochLean.Probability.Process.Stopping.Finite

/-! # Sampling conditional projections at countable-valued stopping times

The input family need not be adapted, and its conditional projection need
not be a martingale. Countable stopping fibers allow the coordinate identities
to be combined. Integrability of the sampled input is explicit; neither
deterministic integrability alone nor coordinate AE identities justify it.
-/

@[expose] public section

open MeasureTheory Filter Set
open scoped NNReal

namespace ProbabilityTheory.FiniteStoppingTime

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsFiniteMeasure P]
  {F : Filtration ℝ≥0 mΩ} {X Y : ℝ≥0 → Ω → ℝ}

theorem sample_condExp_of_countable_range (σ : FiniteStoppingTime F)
    (hcount : (range σ).Countable) (hi : ∀ t, Integrable (X t) P)
    (hσi : Integrable (fun ω ↦ X (σ ω) ω) P)
    (he : ∀ t, Y t =ᵐ[P] P[X t | F t]) :
    (fun ω ↦ Y (σ ω) ω) =ᵐ[P] P[(fun ω ↦ X (σ ω) ω) | σ.measurableSpace] := by
  have hlocal (t : ℝ≥0) :
      (fun ω ↦ Y (σ ω) ω) =ᵐ[P.restrict {ω | σ ω = t}]
        P[(fun ω ↦ X (σ ω) ω) | σ.measurableSpace] := by
    have hfiber : MeasurableSet[σ.measurableSpace] {ω | σ ω = t} := by
      simpa only [WithTop.coe_inj] using σ.isStoppingTime.measurableSet_eq' t
    have hsub : (fun ω ↦ X (σ ω) ω) =ᵐ[P.restrict {ω | σ ω = t}] X t := by
      change ∀ᵐ ω ∂P.restrict {ω | σ ω = t}, X (σ ω) ω = X t ω
      rw [ae_restrict_iff' (σ.measurableSpace_le _ hfiber)]
      exact Eventually.of_forall fun ω hω ↦ by rw [show σ ω = t from hω]
    have hce := condExp_congr_ae_restrict σ.measurableSpace_le hfiber hσi (hi t) hsub
    have hfield : P[X t | σ.measurableSpace] =ᵐ[P.restrict {ω | σ ω = t}] P[X t | F t] := by
      have h :=
        condExp_stopping_time_ae_eq_restrict_eq (μ := P) (f := X t) σ.isStoppingTime t
      change P[X t | σ.measurableSpace] =ᵐ[P.restrict {ω | (σ ω : WithTop ℝ≥0) = t}]
        P[X t | F t] at h
      have hset : {ω | (σ ω : WithTop ℝ≥0) = t} = {ω | σ ω = t} := by
        ext ω
        exact WithTop.coe_inj
      rw [hset] at h
      exact h
    have hY : (fun ω ↦ Y (σ ω) ω) =ᵐ[P.restrict {ω | σ ω = t}] Y t := by
      change ∀ᵐ ω ∂P.restrict {ω | σ ω = t}, Y (σ ω) ω = Y t ω
      rw [ae_restrict_iff' (σ.measurableSpace_le _ hfiber)]
      exact Eventually.of_forall fun ω hω ↦ by rw [show σ ω = t from hω]
    have hcoord : Y t =ᵐ[P.restrict {ω | σ ω = t}] P[X t | F t] :=
      ae_restrict_of_ae (he t)
    exact hY.trans (hcoord.trans (hce.trans hfield).symm)
  let : Countable (range σ) := hcount.to_subtype
  have hall : ∀ᵐ ω ∂P, ∀ t : range σ, σ ω = t →
      Y (σ ω) ω = P[(fun ω ↦ X (σ ω) ω) | σ.measurableSpace] ω := by
    rw [ae_all_iff]
    intro t
    have hmeas : MeasurableSet {ω | σ ω = (t : ℝ≥0)} := by
      apply σ.measurableSpace_le
      simpa only [WithTop.coe_inj] using σ.isStoppingTime.measurableSet_eq' (t : ℝ≥0)
    exact (ae_restrict_iff' hmeas).mp (hlocal t)
  filter_upwards [hall] with ω hω
  exact hω ⟨σ ω, mem_range_self ω⟩ rfl

end ProbabilityTheory.FiniteStoppingTime
