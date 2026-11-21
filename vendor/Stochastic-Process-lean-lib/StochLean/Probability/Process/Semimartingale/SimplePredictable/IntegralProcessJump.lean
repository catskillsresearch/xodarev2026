/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.Semimartingale.SimplePredictable.IntegralProcess
public import StochLean.Probability.Process.Path.LeftLimitStopping
public import Mathlib.Topology.Order.DenselyOrdered

/-! # Jumps of the source elementary integral process

Actual left limits of the finite stopped summands give the formula at every time.
The coefficient on `(T_i,T_(i+1)]` is used at its right endpoint, with the separate
initial coefficient at zero. Repeated endpoints and unbounded coefficients are allowed.
-/

@[expose] public section

open MeasureTheory Filter Set Finset
open scoped NNReal Topology

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {F : Filtration ℝ≥0 mΩ}
  {X : ℝ≥0 → Ω → ℝ} {ω : Ω}

theorem SimplePredictableRep.jumpProcess_integralProcess (H : SimplePredictableRep F)
    (hX : IsCadlagPath (X · ω)) (t : ℝ≥0) :
    jumpProcess (H.integralProcess X) t ω = H.toProcess t ω * jumpProcess X t ω := by
  by_cases ht : t = 0
  · subst t
    simp only [jumpProcess_zero, H.integralProcess_zero, H.toProcess_zero]
  · let : (𝓝[<] t).NeBot := nhdsLT_neBot_of_exists_lt ⟨0, pos_iff_ne_zero.mpr ht⟩
    let L : ℝ≥0 → ℝ := fun a ↦ if a < t then X a ω else leftLimitProcess X t ω
    have hlim : Tendsto (fun s ↦ H.integralProcess X s ω) (𝓝[<] t)
        (𝓝 (H.initial ω * X 0 ω + ∑ i : Fin H.partition.size, H.coefficient i ω *
          (L (H.partition.point i.succ ω) - L (H.partition.point i.castSucc ω)))) := by
      have hs := tendsto_finsetSum univ (fun i (_ : i ∈ (univ : Finset (Fin H.partition.size))) ↦
        ((hX.tendsto_min_const_nhdsLT ht (H.partition.point i.succ ω)).sub
          (hX.tendsto_min_const_nhdsLT ht (H.partition.point i.castSucc ω))).const_mul
            (H.coefficient i ω))
      simpa only [H.integralProcess_apply, L] using hs.const_add (H.initial ω * X 0 ω)
    have hleft : leftLimitProcess (H.integralProcess X) t ω =
        H.initial ω * X 0 ω + ∑ i : Fin H.partition.size, H.coefficient i ω *
          (L (H.partition.point i.succ ω) - L (H.partition.point i.castSucc ω)) := by
      simp only [leftLimitProcess, if_neg ht]
      exact leftLim_eq_of_tendsto hlim
    change H.integralProcess X t ω - leftLimitProcess (H.integralProcess X) t ω = _
    rw [hleft, H.integralProcess_apply]
    simp only [SimplePredictableRep.toProcess, if_neg ht]
    rw [add_sub_add_left_eq_sub, ← Finset.sum_sub_distrib, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i _
    have horder : H.partition.point i.castSucc ω ≤ H.partition.point i.succ ω :=
      (H.partition.path ω).left_le_right i
    by_cases hl : H.partition.point i.castSucc ω < t
    · by_cases hr : t ≤ H.partition.point i.succ ω
      · simp only [L, if_pos hl, if_neg (not_lt_of_ge hr), min_eq_right hr,
          min_eq_left hl.le, hl, hr, and_self, if_true, jumpProcess, Pi.sub_apply]
        ring
      · have hr' := lt_of_not_ge hr
        simp only [L, if_pos hl, if_pos hr', min_eq_left hl.le, min_eq_left hr'.le,
          hl, hr, and_false, if_false, sub_self, zero_mul]
    · have hl' := le_of_not_gt hl
      have hr := hl'.trans horder
      simp only [L, if_neg hl, if_neg (not_lt_of_ge hr), min_eq_right hl', min_eq_right hr,
        hl, false_and, if_false, sub_self, mul_zero, zero_mul]

theorem IsSimplePredictable.jumpProcess_elementaryIntegralProcess
    {H : ℝ≥0 → Ω → ℝ} (hH : IsSimplePredictable H F) (hX : IsCadlagPath (X · ω)) (t : ℝ≥0) :
    jumpProcess (hH.elementaryIntegralProcess X) t ω = H t ω * jumpProcess X t ω := by
  rw [hH.elementaryIntegralProcess_eq hH.choose hH.choose_spec X]
  simpa only [hH.choose_spec] using hH.choose.jumpProcess_integralProcess hX t

end ProbabilityTheory
