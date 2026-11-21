/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.FiniteVariation.Integral
public import StochLean.Probability.Process.Semimartingale.SimplePredictable.IntegralProcess
public import StochLean.Analysis.PathVariation.StieltjesIntegralSimple

/-! # Agreement of pathwise FV and source elementary integrals

The equality is pathwise, with arbitrary finite coefficients and repeated
stopping endpoints. Both integrals keep the same source initial term.
-/

@[expose] public section

open MeasureTheory StochLean Set
open scoped NNReal

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {F : Filtration ℝ≥0 mΩ}
  (X : ℝ≥0 → Ω → ℝ)
  (hv : ∀ ω, LocallyBoundedVariationOn (fun t ↦ X t ω) univ)
  (hr : ∀ ω, IsRightContinuousPath (fun t ↦ X t ω))

theorem SimplePredictableRep.integrableOn_variationStieltjes (H : SimplePredictableRep F)
    (T : ℝ≥0) (ω : Ω) :
    IntegrableOn (fun t ↦ H.toProcess t ω) (Ioc 0 T)
      (totalVariationStieltjes (fun t ↦ X t ω) (hv ω) (hr ω)).measure := by
  have h := integrableOn_variationStieltjes_finite_step (x := fun t ↦ X t ω)
    (hx := hv ω) (hr := hr ω)
    (fun i : Fin H.partition.size ↦ H.partition.point i.castSucc ω)
    (fun i : Fin H.partition.size ↦ H.partition.point i.succ ω)
    (fun i ↦ H.coefficient i ω) (H.initial ω) T
  simpa only [SimplePredictableRep.toProcess, Set.indicator, mem_Ioc] using h

theorem SimplePredictableRep.finiteVariationIntegral_eq (H : SimplePredictableRep F)
    (T : ℝ≥0) (ω : Ω) :
    finiteVariationIntegral X hv hr H.toProcess T ω =
      H.integral (fun t ω ↦ X (min t T) ω) ω := by
  have h := pathStieltjesIntegral_finite_step (x := fun t ↦ X t ω)
    (hx := hv ω) (hr := hr ω)
    (fun i : Fin H.partition.size ↦ H.partition.point i.castSucc ω)
    (fun i : Fin H.partition.size ↦ H.partition.point i.succ ω)
    (fun i ↦ H.coefficient i ω) (fun i ↦ (H.partition.path ω).left_le_right i)
    (H.initial ω) T
  simpa only [finiteVariationIntegral, SimplePredictableRep.toProcess,
    SimplePredictableRep.integral, Set.indicator, mem_Ioc,
    min_eq_left (show (0 : ℝ≥0) ≤ T from bot_le)] using h

theorem SimplePredictableRep.finiteVariationIntegral_terminal (H : SimplePredictableRep F)
    (ω : Ω) :
    finiteVariationIntegral X hv hr H.toProcess (H.partition.terminal ω) ω = H.integral X ω := by
  rw [H.finiteVariationIntegral_eq X hv hr]
  simp only [SimplePredictableRep.integral,
    min_eq_left (show (0 : ℝ≥0) ≤ H.partition.terminal ω from bot_le)]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  have hb (j : Fin (H.partition.size + 1)) : H.partition.point j ω ≤ H.partition.terminal ω :=
    (H.partition.path ω).point_le_horizon j
  rw [min_eq_left (hb i.succ), min_eq_left (hb i.castSucc)]

theorem IsSimplePredictable.finiteVariationIntegral_eq {H : ℝ≥0 → Ω → ℝ}
    (hH : IsSimplePredictable H F) (T : ℝ≥0) (ω : Ω) :
    finiteVariationIntegral X hv hr H T ω =
      hH.elementaryIntegral (fun t ω ↦ X (min t T) ω) ω := by
  have h := hH.choose.finiteVariationIntegral_eq X hv hr T ω
  rw [hH.choose_spec] at h
  exact h

/-- The canonical source elementary process agrees with the existing pathwise FV integral. -/
theorem IsSimplePredictable.elementaryIntegralProcess_eq_finiteVariationIntegral
    {H : ℝ≥0 → Ω → ℝ} (hH : IsSimplePredictable H F) :
    hH.elementaryIntegralProcess X = finiteVariationIntegral X hv hr H := by
  funext t ω
  exact (hH.finiteVariationIntegral_eq X hv hr t ω).symm

theorem IsSimplePredictable.integrableOn_variationStieltjes {H : ℝ≥0 → Ω → ℝ}
    (hH : IsSimplePredictable H F) (T : ℝ≥0) (ω : Ω) :
    IntegrableOn (fun t ↦ H t ω) (Ioc 0 T)
      (totalVariationStieltjes (fun t ↦ X t ω) (hv ω) (hr ω)).measure := by
  have h := hH.choose.integrableOn_variationStieltjes X hv hr T ω
  rw [hH.choose_spec] at h
  exact h

end ProbabilityTheory
