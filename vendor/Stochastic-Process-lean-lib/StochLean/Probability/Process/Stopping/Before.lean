/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.Path.LeftLimit
public import StochLean.Probability.Process.Stopping.Finite

/-! # Stopping strictly before a random lifetime

`stoppedProcessBefore X tau` is `X` before `tau`, and the strict-left value from
`tau` onwards. At lifetime zero it is zero. At infinite lifetime it is `X` at
every finite time; no value of `X` or of its left limit at infinity is used.
The lifetime need not be a stopping time. This definition alone does not assert
adaptedness of the resulting process for arbitrary lifetimes.
-/

@[expose] public section

open MeasureTheory
open scoped NNReal

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

noncomputable def stoppedProcessBefore (X : ℝ≥0 → Ω → ℝ) (τ : Ω → WithTop ℝ≥0)
    (t : ℝ≥0) (ω : Ω) : ℝ :=
  if (t : WithTop ℝ≥0) < τ ω then X t ω else leftLimitProcess X ((τ ω).untopD 0) ω

theorem stoppedProcessBefore_eq_of_lt (X : ℝ≥0 → Ω → ℝ) {τ : Ω → WithTop ℝ≥0}
    {t : ℝ≥0} {ω : Ω} (ht : (t : WithTop ℝ≥0) < τ ω) :
    stoppedProcessBefore X τ t ω = X t ω := by
  simp only [stoppedProcessBefore, if_pos ht]

theorem stoppedProcessBefore_eq_leftLimit_of_le (X : ℝ≥0 → Ω → ℝ)
    {τ : Ω → WithTop ℝ≥0} {t : ℝ≥0} {ω : Ω} (ht : τ ω ≤ t) :
    stoppedProcessBefore X τ t ω = leftLimitProcess X ((τ ω).untopD 0) ω := by
  simp only [stoppedProcessBefore, if_neg (not_lt_of_ge ht)]

@[simp] theorem stoppedProcessBefore_zero (X : ℝ≥0 → Ω → ℝ) :
    stoppedProcessBefore X (fun _ ↦ 0) = 0 := by
  funext t ω
  rw [stoppedProcessBefore_eq_leftLimit_of_le X (show (0 : WithTop ℝ≥0) ≤ t from bot_le)]
  simp [leftLimitProcess]

@[simp] theorem stoppedProcessBefore_top (X : ℝ≥0 → Ω → ℝ) :
    stoppedProcessBefore X (fun _ ↦ ⊤) = X := by
  funext t ω
  exact stoppedProcessBefore_eq_of_lt X (WithTop.coe_lt_top t)

@[simp] theorem stoppedProcessBefore_const_self (X : ℝ≥0 → Ω → ℝ) (T : ℝ≥0) :
    stoppedProcessBefore X (fun _ ↦ (T : WithTop ℝ≥0)) T = leftLimitProcess X T := by
  funext ω
  rw [stoppedProcessBefore_eq_leftLimit_of_le X le_rfl]
  rfl

theorem Indistinguishable.stoppedProcessBefore {X Y : ℝ≥0 → Ω → ℝ} {P : Measure Ω}
    (h : Indistinguishable X Y P) (τ : Ω → WithTop ℝ≥0) :
    Indistinguishable (stoppedProcessBefore X τ) (stoppedProcessBefore Y τ) P := by
  filter_upwards [h, h.leftLimitProcess] with ω hω hl
  intro t
  simp only [ProbabilityTheory.stoppedProcessBefore, hω, hl]

end ProbabilityTheory
