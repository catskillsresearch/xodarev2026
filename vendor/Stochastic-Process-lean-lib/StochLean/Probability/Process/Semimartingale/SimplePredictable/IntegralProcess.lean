/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.Semimartingale.SimplePredictable.Algebra
public import StochLean.Probability.Process.Path.Stopping

/-! # The source elementary integral process

Protter's `J_X(H)` is the existing elementary integral evaluated against `X` stopped
at the current deterministic time. This is not another general stochastic integral.
The source initial term is retained, including at time zero.
-/

@[expose] public section

open MeasureTheory Finset
open scoped NNReal

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {F : Filtration ℝ≥0 mΩ}

namespace SimplePredictableRep

/-- Representation-level source integral process, using only the existing finite-sum integral. -/
def integralProcess (H : SimplePredictableRep F) (X : ℝ≥0 → Ω → ℝ) : ℝ≥0 → Ω → ℝ :=
  fun t ↦ H.integral (fun s ω ↦ X (min s t) ω)

theorem integralProcess_apply (H : SimplePredictableRep F) (X : ℝ≥0 → Ω → ℝ)
    (t : ℝ≥0) (ω : Ω) :
    H.integralProcess X t ω = H.initial ω * X 0 ω +
      ∑ i, H.coefficient i ω * (X (min (H.partition.point i.succ ω) t) ω -
        X (min (H.partition.point i.castSucc ω) t) ω) := by
  simp only [integralProcess, integral, min_eq_left (show (0 : ℝ≥0) ≤ t from bot_le)]

theorem integralProcess_eq_integral_stopped (H : SimplePredictableRep F)
    (X : ℝ≥0 → Ω → ℝ) (t : ℝ≥0) :
    H.integralProcess X t = H.integral (stoppedProcess X (fun _ ↦ (t : WithTop ℝ≥0))) := by
  rfl

@[simp] theorem integralProcess_zero (H : SimplePredictableRep F)
    (X : ℝ≥0 → Ω → ℝ) (ω : Ω) : H.integralProcess X 0 ω = H.initial ω * X 0 ω := by
  simp [integralProcess_apply]

theorem integralProcess_of_terminal_le (H : SimplePredictableRep F)
    (X : ℝ≥0 → Ω → ℝ) {t : ℝ≥0} {ω : Ω} (ht : H.partition.terminal ω ≤ t) :
    H.integralProcess X t ω = H.integral X ω := by
  have hpoint (i : Fin (H.partition.size + 1)) : H.partition.point i ω ≤ t :=
    (H.partition.monotone_point ω (Fin.le_last i)).trans ht
  simp only [integralProcess_apply, integral, min_eq_left (hpoint _)]

theorem integralProcess_congr (H K : SimplePredictableRep F) (hHK : H.toProcess = K.toProcess)
    (X : ℝ≥0 → Ω → ℝ) : H.integralProcess X = K.integralProcess X := by
  funext t
  exact H.integral_congr K hHK _

theorem integral_stoppedFinite_eq_integralProcess (H : SimplePredictableRep F)
    (X : ℝ≥0 → Ω → ℝ) (τ : FiniteStoppingTime F) (ω : Ω) :
    H.integral (stoppedProcess X τ.withTop) ω = H.integralProcess X (τ ω) ω := by
  rw [τ.stoppedProcess_eq X]
  simp only [integralProcess_apply, integral, min_comm]
  simp

end SimplePredictableRep

namespace IsSimplePredictable

variable {H K : ℝ≥0 → Ω → ℝ}

/-- Protter's source `J_X(H)`, before any extension beyond simple predictable integrands. -/
noncomputable def elementaryIntegralProcess (hH : IsSimplePredictable H F)
    (X : ℝ≥0 → Ω → ℝ) : ℝ≥0 → Ω → ℝ :=
  fun t ↦ hH.elementaryIntegral (fun s ω ↦ X (min s t) ω)

theorem elementaryIntegralProcess_eq (hH : IsSimplePredictable H F)
    (R : SimplePredictableRep F) (hR : R.toProcess = H) (X : ℝ≥0 → Ω → ℝ) :
    hH.elementaryIntegralProcess X = R.integralProcess X := by
  funext t
  exact hH.elementaryIntegral_eq R hR _

theorem elementaryIntegralProcess_eq_elementaryIntegral_stopped
    (hH : IsSimplePredictable H F) (X : ℝ≥0 → Ω → ℝ) (t : ℝ≥0) :
    hH.elementaryIntegralProcess X t =
      hH.elementaryIntegral (stoppedProcess X (fun _ ↦ (t : WithTop ℝ≥0))) := by
  rfl

@[simp] theorem elementaryIntegralProcess_zero (hH : IsSimplePredictable H F)
    (X : ℝ≥0 → Ω → ℝ) (ω : Ω) : hH.elementaryIntegralProcess X 0 ω = H 0 ω * X 0 ω := by
  rw [hH.elementaryIntegralProcess_eq hH.choose hH.choose_spec,
    SimplePredictableRep.integralProcess_zero]
  exact congrArg (fun a ↦ a * X 0 ω)
    (by simpa using congrFun (congrFun hH.choose_spec 0) ω)

theorem elementaryIntegralProcess_add (hH : IsSimplePredictable H F)
    (hK : IsSimplePredictable K F) (X : ℝ≥0 → Ω → ℝ) :
    (hH.add hK).elementaryIntegralProcess X =
      hH.elementaryIntegralProcess X + hK.elementaryIntegralProcess X := by
  funext t
  exact hH.elementaryIntegral_add hK _

theorem elementaryIntegralProcess_sub (hH : IsSimplePredictable H F)
    (hK : IsSimplePredictable K F) (X : ℝ≥0 → Ω → ℝ) :
    (hH.sub hK).elementaryIntegralProcess X =
      hH.elementaryIntegralProcess X - hK.elementaryIntegralProcess X := by
  funext t
  exact hH.elementaryIntegral_sub hK _

theorem elementaryIntegralProcess_smul (hH : IsSimplePredictable H F)
    (c : ℝ) (X : ℝ≥0 → Ω → ℝ) :
    (hH.smul c).elementaryIntegralProcess X = c • hH.elementaryIntegralProcess X := by
  funext t
  exact hH.elementaryIntegral_smul c _

theorem elementaryIntegralProcess_const_initial (hH : IsSimplePredictable H F)
    (Z : Ω → ℝ) :
    hH.elementaryIntegralProcess (fun _ : ℝ≥0 ↦ Z) = fun _ ω ↦ H 0 ω * Z ω := by
  funext t
  exact hH.elementaryIntegral_const_initial Z

theorem elementaryIntegral_stoppedFinite_eq_elementaryIntegralProcess
    (hH : IsSimplePredictable H F) (X : ℝ≥0 → Ω → ℝ) (τ : FiniteStoppingTime F) (ω : Ω) :
    hH.elementaryIntegral (stoppedProcess X τ.withTop) ω =
      hH.elementaryIntegralProcess X (τ ω) ω :=
  hH.choose.integral_stoppedFinite_eq_integralProcess X τ ω

end IsSimplePredictable
end ProbabilityTheory
