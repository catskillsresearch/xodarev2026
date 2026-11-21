/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.Semimartingale.Basic
public import StochLean.Probability.Process.Semimartingale.SimplePredictable.IntegratorAlgebra
public import StochLean.Probability.Process.Path.Algebra

/-! # Linear stability of the source good-integrator predicate

These results use elementary integration and its quantitative continuity
criterion. No classical decomposition or Bichteler-Dellacherie theorem is
assumed in proving stability.
-/

@[expose] public section

open MeasureTheory Filter Set Finset
open scoped NNReal ENNReal Topology

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {F : Filtration ℝ≥0 mΩ}
  {P : Measure Ω} {X Y : ℝ≥0 → Ω → ℝ}

theorem IsGoodIntegrator.add (hX : IsGoodIntegrator X F P) (hY : IsGoodIntegrator Y F P) :
    IsGoodIntegrator (X + Y) F P := by
  apply isGoodIntegrator_iff_continuousAtZero.mpr
  intro ε hε η hη
  obtain ⟨δX, hδX, hXbound⟩ := (isGoodIntegrator_iff_continuousAtZero.mp hX)
    (ε / 2) (half_pos hε) (η / 2) (ENNReal.half_pos hη.ne')
  obtain ⟨δY, hδY, hYbound⟩ := (isGoodIntegrator_iff_continuousAtZero.mp hY)
    (ε / 2) (half_pos hε) (η / 2) (ENNReal.half_pos hη.ne')
  refine ⟨min δX δY, lt_min hδX hδY, ?_⟩
  intro H hH hb
  have hbX := hXbound H hH (fun t ω ↦ (hb t ω).trans (min_le_left _ _))
  have hbY := hYbound H hH (fun t ω ↦ (hb t ω).trans (min_le_right _ _))
  rw [hH.elementaryIntegral_add_integrator]
  have hs : {ω | ε ≤ ‖(hH.elementaryIntegral X + hH.elementaryIntegral Y) ω‖} ⊆
      {ω | ε / 2 ≤ ‖hH.elementaryIntegral X ω‖} ∪
        {ω | ε / 2 ≤ ‖hH.elementaryIntegral Y ω‖} := by
    intro ω hω
    by_contra h
    simp only [mem_union, mem_ofPred_eq, not_or, not_le] at h
    have hn := norm_add_le (hH.elementaryIntegral X ω) (hH.elementaryIntegral Y ω)
    change ε ≤ ‖hH.elementaryIntegral X ω + hH.elementaryIntegral Y ω‖ at hω
    linarith
  calc
    _ ≤ P ({ω | ε / 2 ≤ ‖hH.elementaryIntegral X ω‖} ∪
        {ω | ε / 2 ≤ ‖hH.elementaryIntegral Y ω‖}) := measure_mono hs
    _ ≤ _ := measure_union_le _ _
    _ ≤ η / 2 + η / 2 := add_le_add hbX hbY
    _ = η := ENNReal.add_halves η

theorem IsGoodIntegrator.const_mul (hX : IsGoodIntegrator X F P) (c : ℝ) :
    IsGoodIntegrator (fun t ω ↦ c * X t ω) F P := by
  by_cases hc : c = 0
  · subst c
    simp only [zero_mul]
    exact isGoodIntegrator_zero F P
  apply isGoodIntegrator_iff_continuousAtZero.mpr
  intro ε hε η hη
  have hcpos : 0 < ‖c‖ := norm_pos_iff.mpr hc
  obtain ⟨δ, hδ, hb⟩ := (isGoodIntegrator_iff_continuousAtZero.mp hX)
    (ε / ‖c‖) (div_pos hε hcpos) η hη
  refine ⟨δ, hδ, fun H hH hbound ↦ ?_⟩
  rw [hH.elementaryIntegral_const_mul_integrator]
  apply (measure_mono (show {ω | ε ≤ ‖c * hH.elementaryIntegral X ω‖} ⊆
      {ω | ε / ‖c‖ ≤ ‖hH.elementaryIntegral X ω‖} from ?_)).trans (hb H hH hbound)
  intro ω hω
  change ε ≤ ‖c * hH.elementaryIntegral X ω‖ at hω
  change ε / ‖c‖ ≤ ‖hH.elementaryIntegral X ω‖
  rw [div_le_iff₀ hcpos]
  simpa only [norm_mul, mul_comm] using hω

theorem IsTotalSemimartingale.add (hX : IsTotalSemimartingale X F P)
    (hY : IsTotalSemimartingale Y F P) : IsTotalSemimartingale (X + Y) F P :=
  ⟨fun t ↦ (hX.1 t).add (hY.1 t), hX.2.1.add hY.2.1, hX.2.2.add hY.2.2⟩

theorem IsTotalSemimartingale.const_mul (hX : IsTotalSemimartingale X F P) (c : ℝ) :
    IsTotalSemimartingale (fun t ω ↦ c * X t ω) F P :=
  ⟨fun t ↦ (hX.1 t).const_mul c,
    hX.2.1.continuous_comp (continuous_const.mul continuous_id), hX.2.2.const_mul c⟩

theorem IsSemimartingale.add (hX : IsSemimartingale X F P) (hY : IsSemimartingale Y F P) :
    IsSemimartingale (X + Y) F P := by
  intro t
  exact (hX t).add (hY t)

theorem IsSemimartingale.const_mul (hX : IsSemimartingale X F P) (c : ℝ) :
    IsSemimartingale (fun t ω ↦ c * X t ω) F P := by
  intro t
  exact (hX t).const_mul c

end ProbabilityTheory
