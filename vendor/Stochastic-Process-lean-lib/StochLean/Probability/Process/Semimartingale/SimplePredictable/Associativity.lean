/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.Semimartingale.SimplePredictable.IntegralProcessCell
public import StochLean.Probability.Process.Semimartingale.SimplePredictable.IntegralProcessStopping

/-! # Associativity of source elementary integration

Actual common stopping partitions reduce the proof to the integral increment
on one cell. Both the initial coefficient product and every repeated endpoint
are retained. The integrator is arbitrary; no semimartingale premise is used.
-/

@[expose] public section

open MeasureTheory Finset
open scoped NNReal

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {F : Filtration ℝ≥0 mΩ}

namespace SimplePredictableRep

private theorem integral_integralProcess_of_partition_eq
    (G H : SimplePredictableRep F) (hp : G.partition = H.partition) (X : ℝ≥0 → Ω → ℝ) :
    G.integral (H.integralProcess X) =
      ((show IsSimplePredictable G.toProcess F from ⟨G, rfl⟩).mul
        (show IsSimplePredictable H.toProcess F from ⟨H, rfl⟩)).elementaryIntegral X := by
  rcases G with ⟨π, g0, hg0, g, hg⟩
  rcases H with ⟨ρ, h0, hh0, h, hh⟩
  change π = ρ at hp
  subst ρ
  let G : SimplePredictableRep F := ⟨π, g0, hg0, g, hg⟩
  let H : SimplePredictableRep F := ⟨π, h0, hh0, h, hh⟩
  let R : SimplePredictableRep F :=
    ⟨π, fun ω ↦ g0 ω * h0 ω, hg0.mul hh0,
      fun i ω ↦ g i ω * h i ω, fun i ↦ (hg i).mul (hh i)⟩
  have hR : R.toProcess = G.toProcess * H.toProcess := by
    funext t ω
    change R.toProcess t ω = G.toProcess t ω * H.toProcess t ω
    by_cases ht : t = 0
    · subst t
      simp only [toProcess_zero]
      rfl
    · by_cases hterm : t ≤ π.terminal ω
      · obtain ⟨i, hi⟩ := (π.path ω).exists_cell
          (show (0 : ℝ≥0) < t ∧ t ≤ π.terminal ω from ⟨pos_iff_ne_zero.mpr ht, hterm⟩)
        rw [R.toProcess_eq_coefficient_of_mem_cell (i := i) hi,
          G.toProcess_eq_coefficient_of_mem_cell (i := i) hi,
          H.toProcess_eq_coefficient_of_mem_cell (i := i) hi]
      · rw [R.toProcess_eq_zero_of_terminal_lt (lt_of_not_ge hterm),
          G.toProcess_eq_zero_of_terminal_lt (lt_of_not_ge hterm),
          H.toProcess_eq_zero_of_terminal_lt (lt_of_not_ge hterm), mul_zero]
  rw [IsSimplePredictable.elementaryIntegral_eq _ R hR]
  funext ω
  change g0 ω * H.integralProcess X 0 ω +
      (∑ i : Fin π.size, g i ω * (H.integralProcess X (π.point i.succ ω) ω -
        H.integralProcess X (π.point i.castSucc ω) ω)) =
    (g0 ω * h0 ω) * X 0 ω +
      ∑ i : Fin π.size, (g i ω * h i ω) * (X (π.point i.succ ω) ω - X (π.point i.castSucc ω) ω)
  rw [H.integralProcess_zero]
  have hi (i : Fin π.size) : H.integralProcess X (π.point i.succ ω) ω -
      H.integralProcess X (π.point i.castSucc ω) ω =
        h i ω * (X (π.point i.succ ω) ω - X (π.point i.castSucc ω) ω) :=
    H.integralProcess_increment_cell X i ω
  have hinit : H.initial = h0 := rfl
  simp only [hi, hinit, mul_assoc]

theorem integral_integralProcess (G H : SimplePredictableRep F) (X : ℝ≥0 → Ω → ℝ) :
    G.integral (H.integralProcess X) =
      ((show IsSimplePredictable G.toProcess F from ⟨G, rfl⟩).mul
        (show IsSimplePredictable H.toProcess F from ⟨H, rfl⟩)).elementaryIntegral X := by
  obtain ⟨G', H', hp, hG, hH⟩ := G.exists_common_partition H
  have h := integral_integralProcess_of_partition_eq G' H' hp X
  rw [G'.integral_congr G hG (H'.integralProcess X), H'.integralProcess_congr H hH X] at h
  refine h.trans (IsSimplePredictable.elementaryIntegral_congr _ _ ?_ X)
  rw [hG, hH]

end SimplePredictableRep

namespace IsSimplePredictable

variable {G H : ℝ≥0 → Ω → ℝ}

theorem elementaryIntegral_elementaryIntegralProcess
    (hG : IsSimplePredictable G F) (hH : IsSimplePredictable H F) (X : ℝ≥0 → Ω → ℝ) :
    hG.elementaryIntegral (hH.elementaryIntegralProcess X) = (hG.mul hH).elementaryIntegral X := by
  have h := hG.choose.integral_integralProcess hH.choose X
  change hG.choose.integral (hH.choose.integralProcess X) = _
  refine h.trans (IsSimplePredictable.elementaryIntegral_congr _ (hG.mul hH) ?_ X)
  rw [hG.choose_spec, hH.choose_spec]

theorem elementaryIntegralProcess_elementaryIntegralProcess
    (hG : IsSimplePredictable G F) (hH : IsSimplePredictable H F) (X : ℝ≥0 → Ω → ℝ) :
    hG.elementaryIntegralProcess (hH.elementaryIntegralProcess X) =
      (hG.mul hH).elementaryIntegralProcess X := by
  funext t
  change hG.elementaryIntegral
    (MeasureTheory.stoppedProcess (hH.elementaryIntegralProcess X) (fun _ ↦ (t : WithTop ℝ≥0))) =
      (hG.mul hH).elementaryIntegral (MeasureTheory.stoppedProcess X (fun _ ↦ (t : WithTop ℝ≥0)))
  rw [← hH.elementaryIntegralProcess_stoppedProcess X (fun _ ↦ (t : WithTop ℝ≥0)),
    hG.elementaryIntegral_elementaryIntegralProcess hH]

end IsSimplePredictable

end ProbabilityTheory
