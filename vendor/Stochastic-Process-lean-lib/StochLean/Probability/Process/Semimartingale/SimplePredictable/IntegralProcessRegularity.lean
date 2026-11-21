/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.Semimartingale.SimplePredictable.IntegralProcess
public import StochLean.Probability.Process.Semimartingale.SimplePredictable.Measurability
public import StochLean.Probability.Process.Stopping.Coefficient
public import StochLean.Probability.Process.Path.Algebra

/-! # Adaptedness and cadlag paths of the source elementary integral process

The coefficient is revealed only strictly after its left endpoint; before that endpoint
the stopped increment vanishes. Thus no anticipative coefficient measurability is assumed.
Path regularity is pathwise and needs no coefficient bound or integrability hypothesis.
-/

@[expose] public section

open MeasureTheory Finset
open scoped NNReal

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {F : Filtration ℝ≥0 mΩ}
  {P : Measure Ω} {X : ℝ≥0 → Ω → ℝ}

namespace SimplePredictableRep

theorem isCadlagPath_integralProcess (H : SimplePredictableRep F) {ω : Ω}
    (hX : IsCadlagPath (X · ω)) : IsCadlagPath (H.integralProcess X · ω) := by
  have hsum := IsCadlagPath.finset_sum Finset.univ
    (fun i : Fin H.partition.size ↦ fun t : ℝ≥0 ↦ H.coefficient i ω *
      (X (min (H.partition.point i.succ ω) t) ω -
        X (min (H.partition.point i.castSucc ω) t) ω)) (fun i _ ↦ by
      have hb := hX.min_const (H.partition.point i.succ ω)
      have ha := hX.min_const (H.partition.point i.castSucc ω)
      have hd := hb.add (ha.continuous_comp continuous_neg)
      have hm := hd.continuous_comp
        (f := fun a : ℝ ↦ H.coefficient i ω * a) (continuous_const.mul continuous_id)
      change IsCadlagPath (fun t ↦ H.coefficient i ω *
        (X (min t (H.partition.point i.succ ω)) ω +
          -X (min t (H.partition.point i.castSucc ω)) ω)) at hm
      simpa only [sub_eq_add_neg, min_comm] using hm)
  have hc : IsCadlagPath (fun _ : ℝ≥0 ↦ H.initial ω * X 0 ω) :=
    IsContinuousPath.isCadlagPath continuous_const
  simp only [integralProcess_apply]
  exact hc.add hsum

theorem hasCadlagPaths_integralProcess (H : SimplePredictableRep F)
    (hX : HasCadlagPaths X P) : HasCadlagPaths (H.integralProcess X) P :=
  hX.mono fun _ hω ↦ H.isCadlagPath_integralProcess hω

theorem adapted_integralProcess (H : SimplePredictableRep F) (hX : Adapted F X)
    (hF : F.IsUsual P) (hr : HasRightContinuousPaths X P) :
    Adapted F (H.integralProcess X) := by
  intro t
  have hm (τ : FiniteStoppingTime F) :
      Measurable[F t] (fun ω ↦ X (min (τ ω) t) ω) := by
    have hs := (hX.stronglyAdapted.stoppedProcess_of_usual hF hr τ.isStoppingTime).adapted t
    change Measurable[F t] (stoppedProcess X τ.withTop t) at hs
    simpa only [τ.stoppedProcess_eq X, min_comm] using hs
  have hterm (i : Fin H.partition.size) : Measurable[F t] (fun ω ↦ H.coefficient i ω *
      (X (min (H.partition.point i.succ ω) t) ω -
        X (min (H.partition.point i.castSucc ω) t) ω)) := by
    have hc := (H.partition.point i.castSucc).measurable_indicator_lt
      (H.measurable_coefficient i) t
    have heq : (fun ω ↦ H.coefficient i ω *
        (X (min (H.partition.point i.succ ω) t) ω -
          X (min (H.partition.point i.castSucc ω) t) ω)) =
        fun ω ↦ (if H.partition.point i.castSucc ω < t then H.coefficient i ω else 0) *
          (X (min (H.partition.point i.succ ω) t) ω -
            X (min (H.partition.point i.castSucc ω) t) ω) := by
      funext ω
      by_cases ht : H.partition.point i.castSucc ω < t
      · simp only [if_pos ht]
      · have ha := le_of_not_gt ht
        have hb : t ≤ H.partition.point i.succ ω :=
          ha.trans ((H.partition.path ω).left_le_right i)
        simp only [if_neg ht, min_eq_right ha, min_eq_right hb, sub_self, mul_zero]
    rw [heq]
    exact hc.mul ((hm _).sub (hm _))
  have hi := (H.measurable_initial.mono (F.mono (show (0 : ℝ≥0) ≤ t from bot_le)) le_rfl).mul
    ((hX 0).mono (F.mono (show (0 : ℝ≥0) ≤ t from bot_le)) le_rfl)
  have hs := hi.add (Finset.measurable_fun_sum univ (fun i _ ↦ hterm i))
  change Measurable[F t] (fun ω ↦ H.integralProcess X t ω)
  simp only [integralProcess_apply]
  exact hs

end SimplePredictableRep

namespace IsSimplePredictable

variable {H : ℝ≥0 → Ω → ℝ}

theorem isCadlagPath_elementaryIntegralProcess (hH : IsSimplePredictable H F) {ω : Ω}
    (hX : IsCadlagPath (X · ω)) : IsCadlagPath (hH.elementaryIntegralProcess X · ω) :=
  hH.choose.isCadlagPath_integralProcess hX

theorem hasCadlagPaths_elementaryIntegralProcess (hH : IsSimplePredictable H F)
    (hX : HasCadlagPaths X P) : HasCadlagPaths (hH.elementaryIntegralProcess X) P :=
  hH.choose.hasCadlagPaths_integralProcess hX

theorem adapted_elementaryIntegralProcess (hH : IsSimplePredictable H F) (hX : Adapted F X)
    (hF : F.IsUsual P) (hr : HasRightContinuousPaths X P) :
    Adapted F (hH.elementaryIntegralProcess X) :=
  hH.choose.adapted_integralProcess hX hF hr

end IsSimplePredictable
end ProbabilityTheory
