/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Analysis.PathVariation.Basic
public import StochLean.Probability.Process.Stopping.Finite

/-! # Finite stopping-time partitions and deterministic embedding -/

@[expose] public section

open MeasureTheory Filter
open scoped NNReal Topology

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

/-- The ordered endpoints are finite at every sample. Repeated endpoints are legal. -/
structure StoppingTimePartition (F : Filtration ℝ≥0 mΩ) where
  size : ℕ
  point : Fin (size + 1) → FiniteStoppingTime F
  monotone_point : ∀ ω, Monotone (fun i ↦ point i ω)
  first_eq_zero : ∀ ω, point 0 ω = 0

namespace StoppingTimePartition

variable {F : Filtration ℝ≥0 mΩ}

def terminal (π : StoppingTimePartition F) : FiniteStoppingTime F := π.point (Fin.last π.size)

/-- Each trajectory is a partition in the same pure deterministic owner. -/
def path (π : StoppingTimePartition F) (ω : Ω) : StochLean.TimePartition (π.terminal ω) where
  size := π.size
  point := fun i ↦ π.point i ω
  monotone_point := π.monotone_point ω
  first_eq_zero := π.first_eq_zero ω
  last_eq_horizon := rfl

def mesh (π : StoppingTimePartition F) (ω : Ω) : ℝ≥0 := (π.path ω).mesh

def deterministic (F : Filtration ℝ≥0 mΩ) {T : ℝ≥0} (π : StochLean.TimePartition T) :
    StoppingTimePartition F where
  size := π.size
  point := fun i ↦ FiniteStoppingTime.const F (π.point i)
  monotone_point := fun _ ↦ π.monotone_point
  first_eq_zero := fun _ ↦ π.first_eq_zero

@[simp] theorem deterministic_terminal {T : ℝ≥0} (π : StochLean.TimePartition T) (ω : Ω) :
    (deterministic F π).terminal ω = T := π.last_eq_horizon

@[simp] theorem deterministic_mesh {T : ℝ≥0} (π : StochLean.TimePartition T) (ω : Ω) :
    (deterministic F π).mesh ω = π.mesh := rfl

/-- Protter's random partitions tending to the identity: both limits hold on one event. -/
def IsTendingToIdentity (π : ℕ → StoppingTimePartition F) (P : Measure Ω) : Prop :=
  ∀ᵐ ω ∂P, Tendsto (fun n ↦ (π n).terminal ω) atTop atTop ∧
    Tendsto (fun n ↦ (π n).mesh ω) atTop (𝓝 0)

theorem isTendingToIdentity_deterministic {P : Measure Ω} {T : ℕ → ℝ≥0}
    (π : (n : ℕ) → StochLean.TimePartition (T n)) (hT : Tendsto T atTop atTop)
    (hmesh : Tendsto (fun n ↦ (π n).mesh) atTop (𝓝 0)) :
    IsTendingToIdentity (fun n ↦ deterministic F (π n)) P := by
  apply ae_of_all
  intro ω
  simpa only [deterministic_terminal, deterministic_mesh] using And.intro hT hmesh

end StoppingTimePartition
end ProbabilityTheory
