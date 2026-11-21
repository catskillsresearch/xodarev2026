/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.Semimartingale.SimplePredictable.IntegralProcess
public import StochLean.Probability.Process.Stopping.Coefficient
public import StochLean.Probability.Process.Stopping.PredictableProcess
public import StochLean.Probability.Process.Path.Step

/-! # The actual elementary integral preserves predictable integrators

In each original simple-predictable cell, the coefficient is measurable
at its left stopping endpoint, not necessarily strictly before it. Its
strictly-after-endpoint step is adapted and left-continuous, hence
predictable. Before and at that endpoint the stopped integrator increment
vanishes exactly, so inserting this strict cutoff does not change the
actual integral. Stopping the predictable integrator preserves its original
predictability for arbitrary stopping times.

The original initial coefficient times the integrator's initial value is
retained as an initial-measurable constant process. No measure, usual
conditions, path regularity, finite variation, coefficient bounds, or
integrability assumptions are needed. The representation and the existing
elementary integral process owner are unchanged.
-/

@[expose] public section

open MeasureTheory Finset
open scoped NNReal

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {F : Filtration ℝ≥0 mΩ}
  {A : ℝ≥0 → Ω → ℝ}

/-- The existing representation-level integral is predictable when its
integrator is predictable, with the original stopping-endpoint coefficients. -/
theorem SimplePredictableRep.isStronglyPredictable_integralProcess
    (R : SimplePredictableRep F) (hA : IsStronglyPredictable F A) :
    IsStronglyPredictable F (R.integralProcess A) := by
  have hstop (τ : FiniteStoppingTime F) :
      IsStronglyPredictable F (fun t ω ↦ A (min (τ ω) t) ω) := by
    have hp := hA.stoppedProcess τ.isStoppingTime
    change IsStronglyPredictable F (MeasureTheory.stoppedProcess A τ.withTop) at hp
    simpa only [τ.stoppedProcess_eq A, min_comm] using hp
  have hterm (i : Fin R.partition.size) : IsStronglyPredictable F
      (fun t ω ↦ R.coefficient i ω *
        (A (min (R.partition.point i.succ ω) t) ω -
          A (min (R.partition.point i.castSucc ω) t) ω)) := by
    have haC : Adapted F (fun t ω ↦
        if R.partition.point i.castSucc ω < t then R.coefficient i ω else 0) :=
      fun t ↦ (R.partition.point i.castSucc).measurable_indicator_lt
        (R.measurable_coefficient i) t
    have hpC := haC.isStronglyPredictable_of_leftContinuous
      (fun ω ↦ (isCagladPath_step_Ioi
        (R.partition.point i.castSucc ω) (R.coefficient i ω)).1)
    have he : (fun t ω ↦ R.coefficient i ω *
        (A (min (R.partition.point i.succ ω) t) ω -
          A (min (R.partition.point i.castSucc ω) t) ω)) =
        fun t ω ↦ (if R.partition.point i.castSucc ω < t then R.coefficient i ω else 0) *
          (A (min (R.partition.point i.succ ω) t) ω -
            A (min (R.partition.point i.castSucc ω) t) ω) := by
      funext t ω
      by_cases ht : R.partition.point i.castSucc ω < t
      · simp only [if_pos ht]
      · have hl := le_of_not_gt ht
        have hr : t ≤ R.partition.point i.succ ω :=
          hl.trans ((R.partition.path ω).left_le_right i)
        simp only [if_neg ht, min_eq_right hl, min_eq_right hr, sub_self, mul_zero]
    rw [he]
    exact hpC.mul ((hstop (R.partition.point i.succ)).sub
      (hstop (R.partition.point i.castSucc)))
  have hi : Measurable[F 0] (fun ω ↦ R.initial ω * A 0 ω) :=
    R.measurable_initial.mul (hA.stronglyAdapted.adapted 0)
  have haI : Adapted F (fun (_ : ℝ≥0) ω ↦ R.initial ω * A 0 ω) :=
    fun _ ↦ hi.mono (F.mono bot_le) le_rfl
  have hpI := haI.isStronglyPredictable_of_leftContinuous
    (fun _ _ ↦ continuousWithinAt_const)
  let : MeasurableSpace (ℝ≥0 × Ω) := F.predictable
  change StronglyMeasurable (fun p : ℝ≥0 × Ω ↦ R.integralProcess A p.1 p.2)
  convert hpI.add (Finset.stronglyMeasurable_sum univ (fun i _ ↦ hterm i)) using 1
  funext p
  simp only [Function.uncurry, Pi.add_apply, Finset.sum_apply,
    SimplePredictableRep.integralProcess_apply]

/-- The actual representation-independent elementary integral process
preserves predictability of the integrator, including its source initial term. -/
theorem IsSimplePredictable.isStronglyPredictable_elementaryIntegralProcess
    {H : ℝ≥0 → Ω → ℝ} (hH : IsSimplePredictable H F) (hA : IsStronglyPredictable F A) :
    IsStronglyPredictable F (hH.elementaryIntegralProcess A) :=
  hH.choose.isStronglyPredictable_integralProcess hA

end ProbabilityTheory
