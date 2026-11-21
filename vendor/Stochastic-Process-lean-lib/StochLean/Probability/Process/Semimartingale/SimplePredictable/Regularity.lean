/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.Semimartingale.SimplePredictable
public import StochLean.Probability.Process.Stopping.Coefficient
public import StochLean.Probability.Process.Path.Step
public import StochLean.Probability.Process.Measurability.Predictable

/-! # Source simple predictable processes really are adapted, caglad and predictable

Coefficient measurability is used at the original left stopping endpoint. Neither
bounded coefficients nor strict separation of endpoints is assumed.
-/

@[expose] public section

open MeasureTheory Finset
open scoped NNReal

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {F : Filtration ℝ≥0 mΩ}

theorem SimplePredictableRep.adapted (H : SimplePredictableRep F) : Adapted F H.toProcess := by
  intro t
  by_cases ht : t = 0
  · subst t
    have heq : H.toProcess 0 = H.initial := funext (H.toProcess_zero)
    rw [heq]
    exact H.measurable_initial
  · change Measurable[F t] (fun ω ↦ if t = 0 then H.initial ω else _)
    simp only [if_neg ht]
    exact Finset.measurable_fun_sum _ (fun i _ ↦
      (H.partition.point i.castSucc).measurable_interval_coefficient
        (H.partition.point i.succ) (H.measurable_coefficient i) t)

theorem SimplePredictableRep.isCagladPath (H : SimplePredictableRep F) (ω : Ω) :
    IsCagladPath (fun t ↦ H.toProcess t ω) := by
  have hsum := IsCagladPath.finset_sum Finset.univ
    (fun i : Fin H.partition.size ↦ fun t : ℝ≥0 ↦
      if H.partition.point i.castSucc ω < t ∧ t ≤ H.partition.point i.succ ω
      then H.coefficient i ω else 0)
    (fun i _ ↦ isCagladPath_step_Ioc ((H.partition.path ω).left_le_right i) (H.coefficient i ω))
  have h := (isCagladPath_initialSpike (H.initial ω)).add hsum
  convert h using 1
  funext t
  change (if t = 0 then H.initial ω else _) = (if t = 0 then H.initial ω else 0) + _
  by_cases ht : t = 0
  · subst t
    have hzero (i : Fin H.partition.size) : ¬ H.partition.point i.castSucc ω < 0 :=
      not_lt_of_ge bot_le
    simp only [hzero, false_and, if_false, Finset.sum_const_zero, add_zero]
  · simp only [if_neg ht, zero_add]

theorem SimplePredictableRep.isStronglyPredictable (H : SimplePredictableRep F) :
    IsStronglyPredictable F H.toProcess :=
  H.adapted.isStronglyPredictable_of_leftContinuous (fun ω ↦ (H.isCagladPath ω).1)

theorem IsSimplePredictable.adapted {H : ℝ≥0 → Ω → ℝ} (hH : IsSimplePredictable H F) :
    Adapted F H := by
  rw [← hH.choose_spec]
  exact hH.choose.adapted

theorem IsSimplePredictable.isCagladPath {H : ℝ≥0 → Ω → ℝ} (hH : IsSimplePredictable H F)
    (ω : Ω) : IsCagladPath (fun t ↦ H t ω) := by
  rw [← hH.choose_spec]
  exact hH.choose.isCagladPath ω

theorem IsSimplePredictable.hasCagladPaths {H : ℝ≥0 → Ω → ℝ} (hH : IsSimplePredictable H F)
    (P : Measure Ω) : HasCagladPaths H P := ae_of_all _ hH.isCagladPath

theorem IsSimplePredictable.isStronglyPredictable {H : ℝ≥0 → Ω → ℝ}
    (hH : IsSimplePredictable H F) : IsStronglyPredictable F H :=
  hH.adapted.isStronglyPredictable_of_leftContinuous (fun ω ↦ (hH.isCagladPath ω).1)

end ProbabilityTheory
