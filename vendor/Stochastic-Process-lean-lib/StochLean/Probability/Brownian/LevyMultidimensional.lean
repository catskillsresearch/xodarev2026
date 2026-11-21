/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Brownian.LevyVectorIndependence
public import StochLean.Probability.Process.Semimartingale.QuadraticCovariation.OrthogonalClock

/-! # Levy's multidimensional Brownian characterization

Protter II.40 is expressed using Mathlib's existing real Brownian predicate
and independence of the entire coordinate processes. No competing vector
Brownian owner is introduced. The canonical raw diagonal bracket condition
forces zero initial values; the continuous-bracket variant states them.
-/

@[expose] public section

open MeasureTheory
open scoped NNReal

namespace ProbabilityTheory

variable {ι Ω : Type*} [Finite ι] {mΩ : MeasurableSpace Ω}
  {P : Measure Ω} [IsProbabilityMeasure P] {F : Filtration ℝ≥0 mΩ}
  {X : ι → ℝ≥0 → Ω → ℝ}

theorem levy_multidimensional_of_continuous_brackets
    (hX : ∀ i, IsContinuousLocalMartingale (X i) F P) (hF : F.IsUsual P)
    (hd : ∀ i, Indistinguishable
      (((hX i).isSemimartingale hF).continuousQuadraticVariation hF) (fun t _ ↦ (t : ℝ)) P)
    (ho : ∀ i j, i ≠ j → Indistinguishable
      (((hX i).isSemimartingale hF).continuousQuadraticCovariation
        ((hX j).isSemimartingale hF) hF) 0 P)
    (h0 : ∀ i, ∀ᵐ ω ∂P, X i 0 ω = 0) :
    (∀ i, IsBrownianReal (X i) P) ∧ iIndepFun (fun i ω t ↦ X i t ω) P :=
  ⟨fun i ↦ (hX i).isBrownianReal_of_continuousBracket_eq_time hF (hd i) (h0 i),
    iIndepFun_coordinate_processes_of_orthogonal hX hF hd ho h0⟩

theorem levy_multidimensional
    (hX : ∀ i, IsContinuousLocalMartingale (X i) F P) (hF : F.IsUsual P)
    (hd : ∀ i, Indistinguishable
      (((hX i).isSemimartingale hF).quadraticVariation hF) (fun t _ ↦ (t : ℝ)) P)
    (ho : ∀ i j, i ≠ j → Indistinguishable
      (((hX i).isSemimartingale hF).quadraticCovariation ((hX j).isSemimartingale hF) hF) 0 P) :
    (∀ i, IsBrownianReal (X i) P) ∧ iIndepFun (fun i ω t ↦ X i t ω) P := by
  have hb (i : ι) := (hX i).isBrownianReal_of_quadraticVariation_eq_time hF (hd i)
  obtain ⟨hcd, hco⟩ := continuous_brackets_of_raw_orthogonal_clock
    (fun i ↦ (hX i).isSemimartingale hF) hF (fun i ↦ (hX i).2)
    (Filter.Eventually.of_forall (fun _ ↦ rfl)) hd ho
  exact ⟨hb, iIndepFun_coordinate_processes_of_orthogonal hX hF hcd hco
    (fun i ↦ (hb i).eval_zero_ae_eq_zero)⟩

end ProbabilityTheory
