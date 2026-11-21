/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.Semimartingale.FiniteSum
public import
  StochLean.Probability.Process.Semimartingale.QuadraticCovariation.ContinuousPartAlgebra

/-! # Finite-sum algebra for the canonical continuous covariation

Only finite intersections of path events are used; the coordinate index
types need not be countable. Every expression uses the existing brackets.
-/

@[expose] public section

open MeasureTheory Filter
open scoped NNReal

namespace ProbabilityTheory

variable {ι κ Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsFiniteMeasure P]
  {F : Filtration ℝ≥0 mΩ} {X : ι → ℝ≥0 → Ω → ℝ} {Y : ℝ≥0 → Ω → ℝ}

theorem continuousQuadraticCovariation_finset_sum_left (S : Finset ι)
    (hX : ∀ i, IsSemimartingale (X i) F P) (hY : IsSemimartingale Y F P) (hF : F.IsUsual P) :
    Indistinguishable ((isSemimartingale_finset_sum S hX).continuousQuadraticCovariation hY hF)
      (fun t ω ↦ ∑ i ∈ S, (hX i).continuousQuadraticCovariation hY hF t ω) P := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    have he : Indistinguishable (∑ i ∈ (∅ : Finset ι), X i)
        (fun t ω ↦ (0 : ℝ) * Y t ω) P := by
      apply Filter.Eventually.of_forall
      intro ω t
      simp
    have hc := (isSemimartingale_finset_sum ∅ hX).continuousQuadraticCovariation_congr
      hY (hY.const_mul 0) hY hF he (Filter.Eventually.of_forall (fun _ _ ↦ rfl))
    filter_upwards [hc, hY.continuousQuadraticCovariation_const_mul_left hY hF 0]
      with ω hcω hzω t
    rw [hcω t, hzω t]
    simp
  | @insert i S hi ih =>
    let hS := isSemimartingale_finset_sum S hX
    have he : Indistinguishable (∑ j ∈ insert i S, X j) (X i + ∑ j ∈ S, X j) P := by
      rw [Finset.sum_insert hi]
      exact Filter.Eventually.of_forall (fun _ _ ↦ rfl)
    have hc := (isSemimartingale_finset_sum (insert i S) hX).continuousQuadraticCovariation_congr
      hY ((hX i).add hS) hY hF he (Filter.Eventually.of_forall (fun _ _ ↦ rfl))
    filter_upwards [hc, (hX i).continuousQuadraticCovariation_add_left hS hY hF, ih]
      with ω hcω haω hiω t
    rw [hcω t, haω t]
    simp only [Pi.add_apply, hiω t, Finset.sum_insert hi]

theorem continuousQuadraticCovariation_finset_sum_right (S : Finset ι)
    (hY : IsSemimartingale Y F P) (hX : ∀ i, IsSemimartingale (X i) F P) (hF : F.IsUsual P) :
    Indistinguishable (hY.continuousQuadraticCovariation (isSemimartingale_finset_sum S hX) hF)
      (fun t ω ↦ ∑ i ∈ S, hY.continuousQuadraticCovariation (hX i) hF t ω) P := by
  have hcomm : ∀ᵐ ω ∂P, ∀ i ∈ S, ∀ t,
      (hX i).continuousQuadraticCovariation hY hF t ω =
        hY.continuousQuadraticCovariation (hX i) hF t ω :=
    (eventually_all_finset S).2 fun i _ ↦ (hX i).continuousQuadraticCovariation_comm hY hF
  filter_upwards [hY.continuousQuadraticCovariation_comm (isSemimartingale_finset_sum S hX) hF,
    continuousQuadraticCovariation_finset_sum_left S hX hY hF, hcomm]
    with ω hcω hsω hiω t
  rw [hcω t, hsω t]
  exact Finset.sum_congr rfl (fun i hi ↦ hiω i hi t)

theorem continuousQuadraticCovariation_finset_sum (S : Finset ι) (T : Finset κ)
    {Y : κ → ℝ≥0 → Ω → ℝ} (hX : ∀ i, IsSemimartingale (X i) F P)
    (hY : ∀ j, IsSemimartingale (Y j) F P) (hF : F.IsUsual P) :
    Indistinguishable ((isSemimartingale_finset_sum S hX).continuousQuadraticCovariation
      (isSemimartingale_finset_sum T hY) hF)
      (fun t ω ↦ ∑ i ∈ S, ∑ j ∈ T, (hX i).continuousQuadraticCovariation (hY j) hF t ω) P := by
  have hr : ∀ᵐ ω ∂P, ∀ i ∈ S, ∀ t,
      (hX i).continuousQuadraticCovariation (isSemimartingale_finset_sum T hY) hF t ω =
        ∑ j ∈ T, (hX i).continuousQuadraticCovariation (hY j) hF t ω :=
    (eventually_all_finset S).2 fun i _ ↦
      continuousQuadraticCovariation_finset_sum_right T (hX i) hY hF
  filter_upwards [continuousQuadraticCovariation_finset_sum_left S hX
    (isSemimartingale_finset_sum T hY) hF, hr] with ω hlω hrω t
  rw [hlω t]
  exact Finset.sum_congr rfl (fun i hi ↦ hrω i hi t)

theorem continuousQuadraticVariation_finset_sum (S : Finset ι)
    (hX : ∀ i, IsSemimartingale (X i) F P) (hF : F.IsUsual P) :
    Indistinguishable ((isSemimartingale_finset_sum S hX).continuousQuadraticVariation hF)
      (fun t ω ↦ ∑ i ∈ S, ∑ j ∈ S, (hX i).continuousQuadraticCovariation (hX j) hF t ω) P :=
  ((isSemimartingale_finset_sum S hX).continuousQuadraticCovariation_self hF).symm.trans
    (continuousQuadraticCovariation_finset_sum S S hX hX hF)

end ProbabilityTheory
