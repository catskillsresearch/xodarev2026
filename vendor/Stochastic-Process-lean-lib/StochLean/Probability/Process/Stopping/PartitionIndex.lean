/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Analysis.PathVariation.CeilingIndex
public import StochLean.Probability.Process.Stopping.Finite
public import StochLean.Probability.Process.Filtration.SubmartingaleReindex
public import Mathlib.Probability.Martingale.OptionalStopping

/-! # Sampling finite stopping times by the existing partition index

The ceiling index is a native discrete stopping time for the reindexed
filtration. When the time already lies on the partition, evaluation is exact.
Discrete integrability and expected-stopping inequalities therefore apply
without introducing a second finite-index stochastic calculus.
-/

@[expose] public section

open StochLean MeasureTheory Filter Set
open scoped NNReal ENNReal

namespace ProbabilityTheory.FiniteStoppingTime

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {F : Filtration ℝ≥0 mΩ} {T : ℝ≥0}

theorem isStoppingTime_ceilingIndex (τ : FiniteStoppingTime F) (π : TimePartition T)
    (hb : ∀ ω, τ ω ≤ T) :
    IsStoppingTime (F.reindex π.pointNat π.pointNat_mono)
      (fun ω ↦ ((π.ceilingIndex (τ ω)).val : WithTop ℕ)) := by
  intro k
  change MeasurableSet[F (π.pointNat k)]
    {ω | ((π.ceilingIndex (τ ω)).val : WithTop ℕ) ≤ k}
  convert τ.isStoppingTime (π.pointNat k) using 1
  ext ω
  simp only [Set.mem_ofPred_eq, ← WithTop.coe_natCast, Nat.cast_id, WithTop.coe_le_coe]
  exact π.ceilingIndex_le_iff (hb ω) k

theorem stoppedValue_ceilingIndex_eq {E : Type*} (X : ℝ≥0 → Ω → E)
    (τ : FiniteStoppingTime F) (π : TimePartition T)
    (hm : ∀ ω, τ ω ∈ Set.range π.point) :
    stoppedValue (fun k ↦ X (π.pointNat k))
      (fun ω ↦ ((π.ceilingIndex (τ ω)).val : WithTop ℕ)) = fun ω ↦ X (τ ω) ω := by
  funext ω
  change X (π.pointNat (π.ceilingIndex (τ ω)).val) ω = X (τ ω) ω
  rw [π.pointNat_ceilingIndex_eq_of_mem (hm ω)]

end ProbabilityTheory.FiniteStoppingTime

namespace MeasureTheory.Submartingale

open ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsFiniteMeasure P]
  {F : Filtration ℝ≥0 mΩ} {X : ℝ≥0 → Ω → ℝ} {T : ℝ≥0}

omit [IsFiniteMeasure P] in
theorem integrable_finiteStoppingTime_value_of_partition (hX : Submartingale X F P)
    (τ : FiniteStoppingTime F) (π : TimePartition T)
    (hm : ∀ ω, τ ω ∈ Set.range π.point) : Integrable (fun ω ↦ X (τ ω) ω) P := by
  have hb (ω) : τ ω ≤ T := by
    obtain ⟨i, hi⟩ := hm ω
    exact hi ▸ π.point_le_horizon i
  have h := (hX.reindex π.pointNat π.pointNat_mono).integrable_stoppedValue
    (τ.isStoppingTime_ceilingIndex π hb)
    (N := π.size) (fun ω ↦ WithTop.coe_le_coe.mpr
      (Nat.le_of_lt_succ (π.ceilingIndex (τ ω)).isLt))
  simpa only [τ.stoppedValue_ceilingIndex_eq X π hm] using h

theorem expected_finiteStoppingTime_mono_of_partition (hX : Submartingale X F P)
    (σ τ : FiniteStoppingTime F) (π : TimePartition T)
    (hσ : ∀ ω, σ ω ∈ Set.range π.point) (hτ : ∀ ω, τ ω ∈ Set.range π.point)
    (hle : ∀ ω, σ ω ≤ τ ω) : (∫ ω, X (σ ω) ω ∂P) ≤ ∫ ω, X (τ ω) ω ∂P := by
  have hs (ω) : σ ω ≤ T := by
    obtain ⟨i, hi⟩ := hσ ω
    exact hi ▸ π.point_le_horizon i
  have ht (ω) : τ ω ≤ T := by
    obtain ⟨i, hi⟩ := hτ ω
    exact hi ▸ π.point_le_horizon i
  have h := (hX.reindex π.pointNat π.pointNat_mono).expected_stoppedValue_mono
    (σ.isStoppingTime_ceilingIndex π hs) (τ.isStoppingTime_ceilingIndex π ht)
    (fun ω ↦ WithTop.coe_le_coe.mpr (π.ceilingIndex_mono (hle ω)))
    (N := π.size) (fun ω ↦ WithTop.coe_le_coe.mpr
      (Nat.le_of_lt_succ (π.ceilingIndex (τ ω)).isLt))
  simpa only [σ.stoppedValue_ceilingIndex_eq X π hσ,
    τ.stoppedValue_ceilingIndex_eq X π hτ] using h

end MeasureTheory.Submartingale
