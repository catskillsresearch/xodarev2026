/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Martingale.Convergence.ContinuousL2Closure
public import StochLean.Probability.Martingale.Convergence.ContinuousLpContraction

/-! # Extending L2 convergence from integer times to the entire half-line

Conditional-expectation contraction controls every later coordinate by an
earlier integer-time error. This is an actual whole-half-line L2 convergence
argument. Almost-sure half-line convergence is not inferred from L2 convergence.
-/

@[expose] public section

open Filter
open scoped NNReal ENNReal Topology

namespace MeasureTheory.Martingale

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsFiniteMeasure P]
  {F : Filtration ℝ≥0 mΩ} {X : ℝ≥0 → Ω → ℝ} {Z : Ω → ℝ}

theorem eLpNorm_increment_le_closing_error (hX : Martingale X F P) (hZ : Integrable Z P)
    (hclose : ∀ t, X t =ᵐ[P] P[Z | F t]) {s t : ℝ≥0} (hst : s ≤ t) :
    eLpNorm (X t - X s) 2 P ≤ eLpNorm (X s - Z) 2 P :=
  hX.eLpNorm_increment_le_closing_error_of_one_le (by norm_num) hZ hclose hst

theorem eLpNorm_sub_closing_le_two (hX : Martingale X F P) (hZ : Integrable Z P)
    (hclose : ∀ t, X t =ᵐ[P] P[Z | F t]) {s t : ℝ≥0} (hst : s ≤ t) :
    eLpNorm (X t - Z) 2 P ≤ 2 * eLpNorm (X s - Z) 2 P :=
  hX.eLpNorm_sub_closing_le_two_of_one_le (by norm_num) hZ hclose hst

theorem tendsto_eLpNorm_two_of_integer_closing
    (hX : Martingale X F P) (hZ : Integrable Z P)
    (hclose : ∀ t, X t =ᵐ[P] P[Z | F t])
    (hn : Tendsto (fun n : ℕ ↦ eLpNorm (X (n : ℝ≥0) - Z) 2 P) atTop (𝓝 0)) :
    Tendsto (fun t : ℝ≥0 ↦ eLpNorm (X t - Z) 2 P) atTop (𝓝 0) :=
  hX.tendsto_eLpNorm_of_integer_closing (by norm_num) hZ hclose hn

end MeasureTheory.Martingale
