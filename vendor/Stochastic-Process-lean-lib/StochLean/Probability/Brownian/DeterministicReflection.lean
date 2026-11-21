/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import Mathlib.Probability.BrownianMotion.Basic
public import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Basic
public import Mathlib.Probability.Distributions.Gaussian.IsGaussianProcess.Basic
public import Mathlib.Probability.Moments.Covariance
public import StochLean.Analysis.PathVariation.Reflection

/-! # Deterministic Brownian reflections

Reflection after a fixed time preserves the entire Brownian finite-dimensional law, not only
one endpoint law. Two reflections flip the increments on one deterministic interval. These are
symmetries used in the reverse-martingale proof of strong quadratic variation.
-/

@[expose] public section

open MeasureTheory
open scoped NNReal ENNReal Topology ProbabilityTheory

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {B : ℝ≥0 → Ω → ℝ}

/-- Reflect a real path after the deterministic time `a`. -/
def reflectAfter (B : ℝ≥0 → Ω → ℝ) (a : ℝ≥0) : ℝ≥0 → Ω → ℝ :=
  fun t ω ↦ StochLean.reflectAfterPath (B · ω) a t

theorem reflectAfter_eq_of_le (a t : ℝ≥0) (h : t ≤ a) (ω : Ω) :
    reflectAfter B a t ω = B t ω := StochLean.reflectAfterPath_eq_of_le (B · ω) h

theorem reflectAfter_eq_of_ge (a t : ℝ≥0) (h : a ≤ t) (ω : Ω) :
    reflectAfter B a t ω = 2 * B a ω - B t ω :=
  StochLean.reflectAfterPath_eq_of_ge (B · ω) h

theorem IsPreBrownianReal.isGaussianProcess_reflectAfter (hB : IsPreBrownianReal B P)
    (a : ℝ≥0) : IsGaussianProcess (reflectAfter B a) P := by
  apply hB.isGaussianProcess.of_isGaussianProcess
  intro t
  classical
  refine ⟨{min t a, t},
    { toFun := fun x ↦ 2 * x ⟨min t a, by simp⟩ - x ⟨t, by simp⟩
      map_add' := by intro x y; simp; ring
      map_smul' := by intro c x; simp; ring }, ?_⟩
  intro ω
  rfl

theorem IsPreBrownianReal.integral_reflectAfter (hB : IsPreBrownianReal B P)
    (a t : ℝ≥0) : ∫ ω, reflectAfter B a t ω ∂P = 0 := by
  change (∫ ω, 2 * B (min t a) ω - B t ω ∂P) = 0
  rw [integral_sub ((hB.integrable_eval _).const_mul 2) (hB.integrable_eval _),
    integral_const_mul, hB.integral_eval, hB.integral_eval]
  ring

theorem IsPreBrownianReal.covariance_reflectAfter (hB : IsPreBrownianReal B P)
    (a s t : ℝ≥0) (hst : s ≤ t) : cov[reflectAfter B a s, reflectAfter B a t; P] = s := by
  let : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  have hlp (u : ℝ≥0) : MemLp (B u) 2 P := (hB.isGaussianProcess.hasGaussianLaw_eval u).memLp_two
  change cov[fun ω ↦ 2 * B (min s a) ω - B s ω,
    fun ω ↦ 2 * B (min t a) ω - B t ω; P] = s
  rw [covariance_fun_sub_fun_sub ((hlp _).const_mul 2) (hlp _) ((hlp _).const_mul 2) (hlp _),
    covariance_const_mul_left, covariance_const_mul_right,
    covariance_const_mul_left, covariance_const_mul_right,
    hB.covariance_eval, hB.covariance_eval, hB.covariance_eval, hB.covariance_eval]
  have hsa : min s a ≤ min t a := min_le_min_right a hst
  have hsat : min s a ≤ t := (min_le_left _ _).trans hst
  rw [min_eq_left hsa, min_eq_left hsat, min_eq_left hst,
    ← min_assoc s t a, min_eq_left hst]
  ring

theorem IsPreBrownianReal.reflectAfter (hB : IsPreBrownianReal B P) (a : ℝ≥0) :
    IsPreBrownianReal (ProbabilityTheory.reflectAfter B a) P :=
  (hB.isGaussianProcess_reflectAfter a).isPreBrownianReal_of_covariance
    (hB.integral_reflectAfter a) (hB.covariance_reflectAfter a)

theorem IsBrownianReal.reflectAfter (hB : IsBrownianReal B P) (a : ℝ≥0) :
    IsBrownianReal (ProbabilityTheory.reflectAfter B a) P := by
  refine ⟨hB.toIsPreBrownianReal.reflectAfter a, ?_⟩
  filter_upwards [hB.cont] with ω hω
  exact (continuous_const.mul (hω.comp (continuous_id.min continuous_const))).sub hω

/-- Process lift of the deterministic interval-increment flip. -/
def flipInterval (B : ℝ≥0 → Ω → ℝ) (a b : ℝ≥0) : ℝ≥0 → Ω → ℝ :=
  fun t ω ↦ StochLean.flipIntervalPath (B · ω) a b t

theorem reflectAfter_reflectAfter (B : ℝ≥0 → Ω → ℝ) {a b : ℝ≥0} (hab : a ≤ b) :
    reflectAfter (reflectAfter B a) b = flipInterval B a b := by
  funext t ω
  exact congrFun (StochLean.reflectAfterPath_reflectAfterPath (B · ω) hab) t

theorem IsPreBrownianReal.flipInterval (hB : IsPreBrownianReal B P) {a b : ℝ≥0}
    (hab : a ≤ b) : IsPreBrownianReal (ProbabilityTheory.flipInterval B a b) P := by
  rw [← reflectAfter_reflectAfter B hab]
  exact (hB.reflectAfter a).reflectAfter b

theorem IsBrownianReal.flipInterval (hB : IsBrownianReal B P) {a b : ℝ≥0}
    (hab : a ≤ b) : IsBrownianReal (ProbabilityTheory.flipInterval B a b) P := by
  rw [← reflectAfter_reflectAfter B hab]
  exact (hB.reflectAfter a).reflectAfter b

end ProbabilityTheory
