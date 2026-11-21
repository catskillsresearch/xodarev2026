/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.Stopping.PartitionIndexField
public import StochLean.Probability.Martingale.OptionalSampling.DiscreteOneSided

/-! # Conditional one-sided sampling on a finite partition

Both stopping values and the conditioning sigma-field are transported exactly
to the native natural-time theorem. Repeated partition points are allowed.
-/

@[expose] public section

open ProbabilityTheory StochLean
open scoped NNReal

namespace MeasureTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsFiniteMeasure P]
  {F : Filtration ℝ≥0 mΩ} {X : ℝ≥0 → Ω → ℝ} {T : ℝ≥0}

theorem Submartingale.finiteStoppingTime_value_ae_le_condExp_of_partition
    (hX : Submartingale X F P) (σ τ : FiniteStoppingTime F) (π : TimePartition T)
    (hσ : ∀ ω, σ ω ∈ Set.range π.point) (hτ : ∀ ω, τ ω ∈ Set.range π.point)
    (hle : ∀ ω, σ ω ≤ τ ω) :
    (fun ω ↦ X (σ ω) ω) ≤ᵐ[P] P[(fun ω ↦ X (τ ω) ω) | σ.measurableSpace] := by
  have hs (ω) : σ ω ≤ T := by
    obtain ⟨i, hi⟩ := hσ ω
    exact hi ▸ π.point_le_horizon i
  have ht (ω) : τ ω ≤ T := by
    obtain ⟨i, hi⟩ := hτ ω
    exact hi ▸ π.point_le_horizon i
  have h := (hX.reindex π.pointNat π.pointNat_mono).stoppedValue_ae_le_condExp_of_le
    (σ.isStoppingTime_ceilingIndex π hs) (τ.isStoppingTime_ceilingIndex π ht)
    (fun ω ↦ WithTop.coe_le_coe.mpr (π.ceilingIndex_mono (hle ω)))
    (N := π.size) (fun ω ↦ WithTop.coe_le_coe.mpr
      (Nat.le_of_lt_succ (π.ceilingIndex (τ ω)).isLt))
  simpa only [σ.stoppedValue_ceilingIndex_eq X π hσ, τ.stoppedValue_ceilingIndex_eq X π hτ,
    σ.measurableSpace_ceilingIndex_eq π hs hσ] using h

theorem Supermartingale.condExp_finiteStoppingTime_value_ae_le_of_partition
    (hX : Supermartingale X F P) (σ τ : FiniteStoppingTime F) (π : TimePartition T)
    (hσ : ∀ ω, σ ω ∈ Set.range π.point) (hτ : ∀ ω, τ ω ∈ Set.range π.point)
    (hle : ∀ ω, σ ω ≤ τ ω) :
    P[(fun ω ↦ X (τ ω) ω) | σ.measurableSpace] ≤ᵐ[P] (fun ω ↦ X (σ ω) ω) := by
  have h := hX.neg.finiteStoppingTime_value_ae_le_condExp_of_partition σ τ π hσ hτ hle
  change (fun ω ↦ -X (σ ω) ω) ≤ᵐ[P]
    P[-(fun ω ↦ X (τ ω) ω) | σ.measurableSpace] at h
  filter_upwards [h, condExp_neg (fun ω ↦ X (τ ω) ω) σ.measurableSpace] with ω hω heω
  rw [heω] at hω
  exact neg_le_neg_iff.mp hω

end MeasureTheory
