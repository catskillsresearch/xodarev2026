/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.Path.Stopping

/-! # Stopped values with an explicitly supplied value at infinity

Mathlib's finite-time stopped value is retained whenever the stopping time is
finite. At infinity the supplied terminal variable is used instead of the
totalized `untopA` evaluation. Truncated stopped values converge to this owner
when the process has the stated full-half-line terminal limit.
-/

@[expose] public section

open Filter ProbabilityTheory
open scoped NNReal Topology

namespace MeasureTheory

variable {Ω E : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
  {X : ℝ≥0 → Ω → E} {Z : Ω → E} {τ : Ω → WithTop ℝ≥0}

/-- Finite stopping uses the existing owner; infinite stopping uses the
explicit terminal variable, never a totalized finite-time value. -/
noncomputable def stoppedValueWithTerminal (X : ℝ≥0 → Ω → E) (Z : Ω → E)
    (τ : Ω → WithTop ℝ≥0) (ω : Ω) : E := by
  classical
  exact if τ ω = ⊤ then Z ω else stoppedValue X τ ω

theorem stoppedValueWithTerminal_of_top {ω : Ω} (hτ : τ ω = ⊤) :
    stoppedValueWithTerminal X Z τ ω = Z ω := by
  simp only [stoppedValueWithTerminal, if_pos hτ]

theorem stoppedValueWithTerminal_of_ne_top {ω : Ω} (hτ : τ ω ≠ ⊤) :
    stoppedValueWithTerminal X Z τ ω = stoppedValue X τ ω := by
  simp only [stoppedValueWithTerminal, if_neg hτ]

@[simp] theorem stoppedValueWithTerminal_coe (u : Ω → ℝ≥0) :
    stoppedValueWithTerminal X Z (fun ω ↦ (u ω : WithTop ℝ≥0)) = fun ω ↦ X (u ω) ω := by
  ext ω
  change (if (u ω : WithTop ℝ≥0) = ⊤ then Z ω else X (u ω) ω) = X (u ω) ω
  exact if_neg WithTop.coe_ne_top

@[simp] theorem stoppedValueWithTerminal_top :
    stoppedValueWithTerminal X Z (fun _ ↦ ⊤) = Z := by
  ext ω
  exact stoppedValueWithTerminal_of_top rfl

theorem ae_tendsto_stoppedValue_truncate_withTerminal [TopologicalSpace E]
    (hlim : ∀ᵐ ω ∂P, Tendsto (fun t : ℝ≥0 ↦ X t ω) atTop (𝓝 (Z ω))) :
    ∀ᵐ ω ∂P, Tendsto
      (fun n : ℕ ↦ stoppedValue X (fun ω ↦ min (τ ω) ((n : ℝ≥0) : WithTop ℝ≥0)) ω)
      atTop (𝓝 (stoppedValueWithTerminal X Z τ ω)) := by
  filter_upwards [hlim] with ω hω
  by_cases hτ : τ ω = ⊤
  · rw [stoppedValueWithTerminal_of_top hτ]
    have he : (fun n : ℕ ↦ stoppedValue X
        (fun ω ↦ min (τ ω) ((n : ℝ≥0) : WithTop ℝ≥0)) ω) =
        (fun n : ℕ ↦ X (n : ℝ≥0) ω) := by
      funext n
      simp only [stoppedValue, hτ, min_eq_right le_top, WithTop.untopA, WithTop.untopD_coe]
    rw [he]
    exact hω.comp tendsto_natCast_atTop_atTop
  · rw [stoppedValueWithTerminal_of_ne_top hτ]
    lift τ ω to ℝ≥0 using hτ with t ht
    obtain ⟨N, hN⟩ := exists_nat_ge t
    apply tendsto_atTop_of_eventually_const (i₀ := N)
    intro n hn
    have htn : (t : WithTop ℝ≥0) ≤ ((n : ℝ≥0) : WithTop ℝ≥0) :=
      WithTop.coe_le_coe.mpr (hN.trans (Nat.cast_le.mpr hn))
    simp only [stoppedValue, ← ht, min_eq_left htn]

theorem ae_norm_stoppedValueWithTerminal_le [SeminormedAddCommGroup E]
    {g : Ω → ℝ} (hX : ∀ᵐ ω ∂P, ∀ t, ‖X t ω‖ ≤ g ω)
    (hZ : ∀ᵐ ω ∂P, ‖Z ω‖ ≤ g ω) :
    ∀ᵐ ω ∂P, ‖stoppedValueWithTerminal X Z τ ω‖ ≤ g ω := by
  filter_upwards [hX, hZ] with ω hXω hZω
  by_cases hτ : τ ω = ⊤
  · simpa only [stoppedValueWithTerminal_of_top hτ] using hZω
  · simpa only [stoppedValueWithTerminal_of_ne_top hτ, stoppedValue] using hXω (τ ω).untopA

end MeasureTheory

namespace ProbabilityTheory.Indistinguishable

open MeasureTheory

variable {Ω E : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
  {X Y : ℝ≥0 → Ω → E} {Z W : Ω → E}

theorem stoppedValueWithTerminal (hXY : Indistinguishable X Y P) (hZW : Z =ᵐ[P] W)
    (τ : Ω → WithTop ℝ≥0) :
    MeasureTheory.stoppedValueWithTerminal X Z τ =ᵐ[P]
      MeasureTheory.stoppedValueWithTerminal Y W τ := by
  filter_upwards [hXY, hZW] with ω hXYω hZWω
  by_cases hτ : τ ω = ⊤
  · simp only [MeasureTheory.stoppedValueWithTerminal_of_top hτ, hZWω]
  · simp only [MeasureTheory.stoppedValueWithTerminal_of_ne_top hτ]
    exact hXYω (τ ω).untopA

end ProbabilityTheory.Indistinguishable
