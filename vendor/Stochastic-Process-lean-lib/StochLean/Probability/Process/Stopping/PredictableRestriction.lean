/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.Stopping.AnnouncingRestriction
public import StochLean.Probability.Process.Stopping.AnnouncingSigma
public import StochLean.Probability.Process.Filtration.StoppingTimeReindex
public import StochLean.Probability.Conditional.EventApproximation

/-! # Restriction of predictable times to pre-stopping events

For `A ∈ F_(T-)`, Levy upward convergence along an announcing filtration gives
eventually correct stopped-measurable event approximations. Tail infima and
integer caps construct announcing data for `T_A`. No general `F_T` event is
substituted for the stronger pre-stopping measurability hypothesis.
-/

@[expose] public section

open MeasureTheory Filter Set
open scoped NNReal Topology

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {F : Filtration ℝ≥0 mΩ}
  {P : Measure Ω} [IsFiniteMeasure P] {τ : Ω → WithTop ℝ≥0}

theorem IsPredictableStoppingTime.restrictedStoppingTime_before
    (hp : IsPredictableStoppingTime F τ P) (hF : F.IsUsual P) {A : Set Ω}
    (hA : MeasurableSet[hp.1.measurableSpaceBefore] A) :
    IsPredictableStoppingTime F (restrictedStoppingTime τ A) P := by
  obtain ⟨σ, hs⟩ := hp.2
  let G := F.stoppingTimeReindex σ hs.isStoppingTime (fun _ _ hij ω ↦ hs.monotone ω hij)
  have hAG : MeasurableSet[⨆ n, G n] A := by
    rw [hs.measurableSpaceBefore_eq_iSup hp.1 hF.complete_initial] at hA
    exact hA
  obtain ⟨B, hB, hBA⟩ := G.exists_measurableSet_eventually_iff (P := P) hAG
  exact hs.predictable_restricted_of_eventual_events hp.1 hF
    (hp.1.measurableSpaceBefore_le A hA) hB hBA

end ProbabilityTheory
