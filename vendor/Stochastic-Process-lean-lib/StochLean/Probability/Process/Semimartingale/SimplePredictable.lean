/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Analysis.PathVariation.StepIntegral
public import StochLean.Probability.Process.Partition

/-!
# Protter simple predictable processes and their elementary integral

The coefficients are finite real random variables, measurable at the left
stopping endpoint. They need not be bounded. A representation is witness data;
the public process is a raw function. Representation independence is proved
before the public integral selector is introduced.
-/

@[expose] public section

open MeasureTheory Finset
open scoped NNReal BigOperators

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

structure SimplePredictableRep (F : Filtration ℝ≥0 mΩ) where
  partition : StoppingTimePartition F
  initial : Ω → ℝ
  measurable_initial : Measurable[F 0] initial
  coefficient : Fin partition.size → Ω → ℝ
  measurable_coefficient : ∀ i, Measurable[(partition.point i.castSucc).measurableSpace]
    (coefficient i)

namespace SimplePredictableRep

variable {F : Filtration ℝ≥0 mΩ}

noncomputable def toProcess (H : SimplePredictableRep F) : ℝ≥0 → Ω → ℝ :=
  fun t ω ↦ if t = 0 then H.initial ω else
    ∑ i, if H.partition.point i.castSucc ω < t ∧ t ≤ H.partition.point i.succ ω
      then H.coefficient i ω else 0

/-- Finite-sum integral on representation data. -/
def integral (H : SimplePredictableRep F) (X : ℝ≥0 → Ω → ℝ) (ω : Ω) : ℝ :=
  H.initial ω * X 0 ω + ∑ i, H.coefficient i ω *
    (X (H.partition.point i.succ ω) ω - X (H.partition.point i.castSucc ω) ω)

@[simp] theorem toProcess_zero (H : SimplePredictableRep F) (ω : Ω) :
    H.toProcess 0 ω = H.initial ω := by simp [toProcess]

/-- Representation independence is pathwise and holds for every integrator. -/
theorem integral_congr (H K : SimplePredictableRep F) (hHK : H.toProcess = K.toProcess)
    (X : ℝ≥0 → Ω → ℝ) : H.integral X = K.integral X := by
  funext ω
  have hinit : H.initial ω = K.initial ω := by
    simpa only [toProcess_zero] using congrFun (congrFun hHK 0) ω
  have hsum := StochLean.sum_intervalIncrement_congr
    (fun i : Fin H.partition.size ↦ H.partition.point i.castSucc ω)
    (fun i : Fin H.partition.size ↦ H.partition.point i.succ ω)
    (fun i : Fin H.partition.size ↦ H.coefficient i ω)
    (fun i : Fin K.partition.size ↦ K.partition.point i.castSucc ω)
    (fun i : Fin K.partition.size ↦ K.partition.point i.succ ω)
    (fun i : Fin K.partition.size ↦ K.coefficient i ω)
    (fun i ↦ (H.partition.path ω).left_le_right i)
    (fun i ↦ (K.partition.path ω).left_le_right i)
    (fun t ht ↦ by
      simpa only [toProcess, ne_of_gt ht, ↓reduceIte] using congrFun (congrFun hHK t) ω)
    (fun t ↦ X t ω)
  exact congrArg₂ (· + ·) (congrArg (fun a ↦ a * X 0 ω) hinit) hsum

def zero (F : Filtration ℝ≥0 mΩ) : SimplePredictableRep F where
  partition := StoppingTimePartition.deterministic F StochLean.TimePartition.empty
  initial := fun _ ↦ 0
  measurable_initial := measurable_const
  coefficient := Fin.elim0
  measurable_coefficient := fun i ↦ Fin.elim0 i

@[simp] theorem toProcess_zeroRep (F : Filtration ℝ≥0 mΩ) :
    (zero F).toProcess = 0 := by
  funext t ω
  by_cases ht : t = 0 <;>
    simp [toProcess, zero, StoppingTimePartition.deterministic, StochLean.TimePartition.empty, ht]

@[simp] theorem integral_zero (F : Filtration ℝ≥0 mΩ) (X : ℝ≥0 → Ω → ℝ) :
    (zero F).integral X = 0 := by
  funext ω
  simp [integral, zero, StoppingTimePartition.deterministic, StochLean.TimePartition.empty]

/-- A deterministic source interval with separate time-zero and positive-time coefficients. -/
def deterministicInterval (F : Filtration ℝ≥0 mΩ) (T : ℝ≥0) (a c : ℝ) :
    SimplePredictableRep F where
  partition := StoppingTimePartition.deterministic F (StochLean.TimePartition.single T)
  initial := fun _ ↦ a
  measurable_initial := measurable_const
  coefficient := fun _ _ ↦ c
  measurable_coefficient := fun _ ↦ measurable_const

theorem integral_deterministicInterval (F : Filtration ℝ≥0 mΩ) (T : ℝ≥0) (a c : ℝ)
    (X : ℝ≥0 → Ω → ℝ) (ω : Ω) :
    (deterministicInterval F T a c).integral X ω = a * X 0 ω + c * (X T ω - X 0 ω) := by
  change a * X 0 ω + (∑ i : Fin 1, c *
    (X ((![0, T] : Fin 2 → ℝ≥0) i.succ) ω -
      X ((![0, T] : Fin 2 → ℝ≥0) i.castSucc) ω)) = _
  rw [Fin.sum_univ_one]
  rfl

/-- R03: the integral on `[0,T]` includes the source initial term. -/
theorem integral_one_closed (F : Filtration ℝ≥0 mΩ) (T : ℝ≥0)
    (X : ℝ≥0 → Ω → ℝ) (ω : Ω) :
    (deterministicInterval F T 1 1).integral X ω = X T ω := by
  rw [integral_deterministicInterval]
  ring

/-- R03: excluding time zero gives the increment of the integrator. -/
theorem integral_one_open (F : Filtration ℝ≥0 mΩ) (T : ℝ≥0)
    (X : ℝ≥0 → Ω → ℝ) (ω : Ω) :
    (deterministicInterval F T 0 1).integral X ω = X T ω - X 0 ω := by
  rw [integral_deterministicInterval]
  ring

end SimplePredictableRep

/-- The source simple predictable class as an extensional predicate on raw processes. -/
def IsSimplePredictable (H : ℝ≥0 → Ω → ℝ) (F : Filtration ℝ≥0 mΩ) : Prop :=
  ∃ R : SimplePredictableRep F, R.toProcess = H

namespace IsSimplePredictable

variable {F : Filtration ℝ≥0 mΩ} {H : ℝ≥0 → Ω → ℝ}

/-- The source elementary integral. Choice is independent of the representation by
`SimplePredictableRep.integral_congr`. It is available only for a simple predictable integrand. -/
noncomputable def elementaryIntegral (hH : IsSimplePredictable H F)
    (X : ℝ≥0 → Ω → ℝ) : Ω → ℝ := hH.choose.integral X

theorem elementaryIntegral_eq (hH : IsSimplePredictable H F)
    (R : SimplePredictableRep F) (hR : R.toProcess = H) (X : ℝ≥0 → Ω → ℝ) :
    hH.elementaryIntegral X = R.integral X :=
  hH.choose.integral_congr R (hH.choose_spec.trans hR.symm) X

theorem elementaryIntegral_proof_irrel (hH hH' : IsSimplePredictable H F)
    (X : ℝ≥0 → Ω → ℝ) : hH.elementaryIntegral X = hH'.elementaryIntegral X := rfl

theorem measurable_initial (hH : IsSimplePredictable H F) : Measurable[F 0] (H 0) := by
  have heq : H 0 = hH.choose.initial := by
    funext ω
    simpa only [SimplePredictableRep.toProcess_zero] using
      (congrFun (congrFun hH.choose_spec 0) ω).symm
  rw [heq]
  exact hH.choose.measurable_initial

/-- A constant integrator retains only the source time-zero term. -/
theorem elementaryIntegral_const_initial (hH : IsSimplePredictable H F) (Z : Ω → ℝ) :
    hH.elementaryIntegral (fun _ : ℝ≥0 ↦ Z) = fun ω ↦ H 0 ω * Z ω := by
  funext ω
  have heq : hH.choose.initial ω = H 0 ω := by
    simpa only [SimplePredictableRep.toProcess_zero] using
      congrFun (congrFun hH.choose_spec 0) ω
  simp [elementaryIntegral, SimplePredictableRep.integral, heq]

theorem zero (F : Filtration ℝ≥0 mΩ) : IsSimplePredictable (0 : ℝ≥0 → Ω → ℝ) F :=
  ⟨SimplePredictableRep.zero F, SimplePredictableRep.toProcess_zeroRep F⟩

@[simp] theorem elementaryIntegral_zero (F : Filtration ℝ≥0 mΩ)
    (X : ℝ≥0 → Ω → ℝ) : (zero F).elementaryIntegral X = 0 := by
  rw [elementaryIntegral_eq _ (SimplePredictableRep.zero F)
    (SimplePredictableRep.toProcess_zeroRep F), SimplePredictableRep.integral_zero]

end IsSimplePredictable
end ProbabilityTheory
