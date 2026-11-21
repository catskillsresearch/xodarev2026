/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import Mathlib.Probability.Process.Stopping

/-! # Everywhere finite stopping times

These are witness data for Protter simple predictable representations, not a
replacement for Mathlib's `IsStoppingTime`. A source endpoint is finite at every
sample, which is stronger than almost-sure finiteness. Evaluation is ordinary
function application and never uses the totalized value at infinity.
-/

@[expose] public section

open MeasureTheory
open scoped NNReal

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

structure FiniteStoppingTime (F : Filtration ℝ≥0 mΩ) where
  toFun : Ω → ℝ≥0
  isStoppingTime : IsStoppingTime F (fun ω ↦ (toFun ω : WithTop ℝ≥0))

namespace FiniteStoppingTime

variable {F : Filtration ℝ≥0 mΩ}

instance : CoeFun (FiniteStoppingTime F) (fun _ ↦ Ω → ℝ≥0) := ⟨toFun⟩

def withTop (τ : FiniteStoppingTime F) : Ω → WithTop ℝ≥0 := fun ω ↦ τ ω

@[simp] theorem withTop_ne_top (τ : FiniteStoppingTime F) (ω : Ω) : τ.withTop ω ≠ ⊤ :=
  WithTop.coe_ne_top

def const (F : Filtration ℝ≥0 mΩ) (t : ℝ≥0) : FiniteStoppingTime F :=
  ⟨fun _ ↦ t, isStoppingTime_const F t⟩

@[simp] theorem const_apply (t : ℝ≥0) (ω : Ω) : const F t ω = t := rfl

def min (τ σ : FiniteStoppingTime F) : FiniteStoppingTime F :=
  ⟨fun ω ↦ Min.min (τ ω) (σ ω), by
    simpa only [WithTop.coe_min] using τ.isStoppingTime.min σ.isStoppingTime⟩

@[simp] theorem min_apply (τ σ : FiniteStoppingTime F) (ω : Ω) :
    τ.min σ ω = Min.min (τ ω) (σ ω) := rfl

def max (τ σ : FiniteStoppingTime F) : FiniteStoppingTime F :=
  ⟨fun ω ↦ Max.max (τ ω) (σ ω), by
    simpa only [WithTop.coe_max] using τ.isStoppingTime.max σ.isStoppingTime⟩

@[simp] theorem max_apply (τ σ : FiniteStoppingTime F) (ω : Ω) :
    τ.max σ ω = Max.max (τ ω) (σ ω) := rfl

/-- The canonical sigma-algebra at this stopping time. -/
@[instance_reducible] def measurableSpace (τ : FiniteStoppingTime F) : MeasurableSpace Ω :=
  τ.isStoppingTime.measurableSpace

theorem measurableSpace_le (τ : FiniteStoppingTime F) : τ.measurableSpace ≤ mΩ :=
  τ.isStoppingTime.measurableSpace_le

theorem stoppedValue_eq {E : Type*} (X : ℝ≥0 → Ω → E) (τ : FiniteStoppingTime F) :
    stoppedValue X τ.withTop = fun ω ↦ X (τ ω) ω := rfl

theorem stoppedProcess_eq {E : Type*} (X : ℝ≥0 → Ω → E) (τ : FiniteStoppingTime F) :
    stoppedProcess X τ.withTop = fun t ω ↦ X (Min.min t (τ ω)) ω := by
  ext t ω
  change X (WithTop.untopA (Min.min (t : WithTop ℝ≥0) (τ ω))) ω = _
  rw [← WithTop.coe_min]
  rfl

/-- Forget the top point only after an everywhere-finiteness proof. -/
noncomputable def ofNotTop {τ : Ω → WithTop ℝ≥0} (hτ : IsStoppingTime F τ)
    (hne : ∀ ω, τ ω ≠ ⊤) : FiniteStoppingTime F :=
  ⟨fun ω ↦ (τ ω).untopA, by
    have heq (ω) : ((τ ω).untopA : WithTop ℝ≥0) = τ ω := by
      rw [WithTop.untopA_eq_untop (hne ω), WithTop.coe_untop]
    simpa only [heq] using hτ⟩

@[simp] theorem withTop_ofNotTop {τ : Ω → WithTop ℝ≥0} (hτ : IsStoppingTime F τ)
    (hne : ∀ ω, τ ω ≠ ⊤) : (ofNotTop hτ hne).withTop = τ := by
  funext ω
  change ((τ ω).untopA : WithTop ℝ≥0) = τ ω
  rw [WithTop.untopA_eq_untop (hne ω), WithTop.coe_untop]

@[simp] theorem measurableSpace_ofNotTop {τ : Ω → WithTop ℝ≥0}
    (hτ : IsStoppingTime F τ) (hne : ∀ ω, τ ω ≠ ⊤) :
    (ofNotTop hτ hne).measurableSpace = hτ.measurableSpace := by
  have heq := withTop_ofNotTop hτ hne
  unfold measurableSpace
  congr 1

/-- A possibly infinite stopping time capped at a deterministic finite time. -/
noncomputable def truncate {τ : Ω → WithTop ℝ≥0} (hτ : IsStoppingTime F τ)
    (t : ℝ≥0) : FiniteStoppingTime F :=
  ofNotTop ((isStoppingTime_const F t).min hτ)
    (fun _ ↦ ne_top_of_le_ne_top WithTop.coe_ne_top (min_le_left _ _))

@[simp] theorem withTop_truncate {τ : Ω → WithTop ℝ≥0} (hτ : IsStoppingTime F τ)
    (t : ℝ≥0) : (truncate hτ t).withTop = fun ω ↦ Min.min (t : WithTop ℝ≥0) (τ ω) :=
  withTop_ofNotTop _ _

theorem truncate_le {τ : Ω → WithTop ℝ≥0} (hτ : IsStoppingTime F τ)
    (t : ℝ≥0) (ω : Ω) : truncate hτ t ω ≤ t :=
  WithTop.untopA_le (min_le_left _ _)

theorem stoppedValue_truncate {E : Type*} (X : ℝ≥0 → Ω → E)
    {τ : Ω → WithTop ℝ≥0} (hτ : IsStoppingTime F τ) (t : ℝ≥0) :
    (fun ω ↦ X (truncate hτ t ω) ω) = stoppedProcess X τ t := rfl

end FiniteStoppingTime
end ProbabilityTheory
