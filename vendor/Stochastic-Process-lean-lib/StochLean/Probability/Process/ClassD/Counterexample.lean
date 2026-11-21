/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.ClassD.Basic
public import StochLean.ForMathlib.Probability.GaussianCriticalExponential

/-! # Deterministic-time UI does not define Class D

An adapted random-time spike is zero almost surely at each deterministic time,
yet a finite stopping time captures a nonintegrable Gaussian exponential.
This example deliberately has no right-continuous paths; it also explains why
Class D is invariant under indistinguishability, not arbitrary modification.
It is not a counterexample to the right-continuous true-martingale bridge.
-/

@[expose] public section

open MeasureTheory Filter
open scoped NNReal

namespace ProbabilityTheory

theorem exists_adapted_uniformIntegrable_not_isClassD :
    ∃ X : ℝ≥0 → ℝ → ℝ,
      Adapted (Filtration.const ℝ≥0 (borel ℝ) le_rfl) X ∧
      UniformIntegrable X 1 (gaussianReal 0 1) ∧
      IsModification X 0 (gaussianReal 0 1) ∧
      ¬ IsClassD X (Filtration.const ℝ≥0 (borel ℝ) le_rfl) (gaussianReal 0 1) := by
  let F := Filtration.const ℝ≥0 (borel ℝ) le_rfl
  let V : ℝ → ℝ := fun ω ↦ Real.exp (ω ^ 2 / 2)
  let X : ℝ≥0 → ℝ → ℝ := fun t ↦ {ω : ℝ | ‖ω‖₊ = t}.indicator V
  let : NullSingletonClass (gaussianReal 0 1) :=
    nullSingletonClass_gaussianReal (by norm_num)
  have hnorm : Measurable (fun ω : ℝ ↦ ‖ω‖₊) := by fun_prop
  have hV : Measurable V := by fun_prop
  have ha : Adapted F X := fun t ↦
    hV.indicator (hnorm (measurableSet_singleton t))
  have hm : IsModification X 0 (gaussianReal 0 1) := by
    intro t
    filter_upwards [(gaussianReal 0 1).ae_ne (t : ℝ),
      (gaussianReal 0 1).ae_ne (-(t : ℝ))] with ω hp hn
    have hne : ‖ω‖₊ ≠ t := by
      intro he
      have he' : |ω| = (t : ℝ) := congrArg (fun r : ℝ≥0 ↦ (r : ℝ)) he
      rcases le_total 0 ω with hω | hω
      · exact hp ((abs_of_nonneg hω).symm.trans he')
      · apply hn
        rw [abs_of_nonpos hω] at he'
        linarith
    exact Set.indicator_of_notMem (s := {ω : ℝ | ‖ω‖₊ = t}) hne V
  have hu : UniformIntegrable X 1 (gaussianReal 0 1) :=
    (uniformIntegrable_const le_rfl (by simp)
      (MemLp.zero : MemLp (fun _ : ℝ ↦ (0 : ℝ)) 1 (gaussianReal 0 1))).ae_eq hm.symm
  refine ⟨X, ha, hu, hm, fun hD ↦ ?_⟩
  let τ : FiniteStoppingTime F := ⟨fun ω ↦ ‖ω‖₊, fun t ↦ by
    change MeasurableSet {ω : ℝ | (‖ω‖₊ : WithTop ℝ≥0) ≤ (t : WithTop ℝ≥0)}
    simpa only [WithTop.coe_le_coe] using
      (measurableSet_le hnorm (measurable_const (a := t)))⟩
  have hi := hD.integrable_finiteStoppingTime_value τ
  have he : (fun ω ↦ X (τ ω) ω) = V := by
    funext ω
    exact Set.indicator_of_mem (s := {x : ℝ | ‖x‖₊ = ‖ω‖₊}) rfl V
  rw [he] at hi
  exact not_integrable_exp_half_sq_gaussianReal hi

end ProbabilityTheory
