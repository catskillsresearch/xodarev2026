/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.Semimartingale.SimplePredictable.IntegralProcess

/-! # Initial-event masks of source simple predictable processes

An initial measurable event is measurable at every source left stopping endpoint.
Masking retains the same partition, including repeated endpoints, and commutes
pathwise with both the terminal elementary integral and its process version.
-/

@[expose] public section

open MeasureTheory Set
open scoped NNReal

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {F : Filtration ℝ≥0 mΩ}

namespace SimplePredictableRep

noncomputable def initialMask (H : SimplePredictableRep F) (s : Set Ω)
    (hs : MeasurableSet[F 0] s) : SimplePredictableRep F where
  partition := H.partition
  initial := s.indicator H.initial
  measurable_initial := H.measurable_initial.indicator hs
  coefficient := fun i ↦ s.indicator (H.coefficient i)
  measurable_coefficient := fun i ↦ (H.measurable_coefficient i).indicator
    ((H.partition.point i.castSucc).isStoppingTime.le_measurableSpace_of_const_le
      (fun _ ↦ bot_le) s hs)

theorem toProcess_initialMask (H : SimplePredictableRep F) {s : Set Ω}
    (hs : MeasurableSet[F 0] s) :
    (H.initialMask s hs).toProcess = fun t ↦ s.indicator (H.toProcess t) := by
  classical
  funext t ω
  change (if t = 0 then s.indicator H.initial ω else
    ∑ i : Fin H.partition.size,
      if H.partition.point i.castSucc ω < t ∧ t ≤ H.partition.point i.succ ω
      then s.indicator (H.coefficient i) ω else 0) = s.indicator (H.toProcess t) ω
  by_cases hω : ω ∈ s <;> simp [toProcess, hω]

theorem integral_initialMask (H : SimplePredictableRep F) {s : Set Ω}
    (hs : MeasurableSet[F 0] s) (X : ℝ≥0 → Ω → ℝ) :
    (H.initialMask s hs).integral X = s.indicator (H.integral X) := by
  classical
  funext ω
  change s.indicator H.initial ω * X 0 ω + ∑ i : Fin H.partition.size,
    s.indicator (H.coefficient i) ω *
      (X (H.partition.point i.succ ω) ω - X (H.partition.point i.castSucc ω) ω) =
        s.indicator (H.integral X) ω
  by_cases hω : ω ∈ s <;> simp [integral, hω]

end SimplePredictableRep

namespace IsSimplePredictable

variable {H : ℝ≥0 → Ω → ℝ} {s : Set Ω}

theorem indicator (hH : IsSimplePredictable H F) (hs : MeasurableSet[F 0] s) :
    IsSimplePredictable (fun t ↦ s.indicator (H t)) F := by
  refine ⟨hH.choose.initialMask s hs, ?_⟩
  rw [SimplePredictableRep.toProcess_initialMask, hH.choose_spec]

theorem elementaryIntegral_indicator (hH : IsSimplePredictable H F)
    (hs : MeasurableSet[F 0] s) (X : ℝ≥0 → Ω → ℝ) :
    (hH.indicator hs).elementaryIntegral X = s.indicator (hH.elementaryIntegral X) := by
  have heq : (hH.choose.initialMask s hs).toProcess = fun t ↦ s.indicator (H t) := by
    rw [SimplePredictableRep.toProcess_initialMask, hH.choose_spec]
  rw [(hH.indicator hs).elementaryIntegral_eq _ heq,
    SimplePredictableRep.integral_initialMask]
  rfl

theorem elementaryIntegralProcess_indicator (hH : IsSimplePredictable H F)
    (hs : MeasurableSet[F 0] s) (X : ℝ≥0 → Ω → ℝ) :
    (hH.indicator hs).elementaryIntegralProcess X =
      fun t ↦ s.indicator (hH.elementaryIntegralProcess X t) := by
  funext t
  exact hH.elementaryIntegral_indicator hs _

end IsSimplePredictable
end ProbabilityTheory
