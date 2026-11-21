/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.FiniteVariation.TerminalVariation
public import StochLean.Probability.Process.FiniteVariation.Stopping
public import StochLean.Probability.Process.Stopping.TerminalValue

/-! # Whole-half-line variation after stopping

The actual extended variation of a stopped path is its variation up to the
stopping time, including the stopping endpoint. Infinite times use the
original whole-half-line variation through the existing terminal-valued
sampling owner. None of these pathwise statements require stopping-time
measurability, cadlag paths, or finite variation.
-/

@[expose] public section

open MeasureTheory StochLean Set
open scoped NNReal ENNReal

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
  {X : ℝ≥0 → Ω → ℝ}

/-- Clipping the half-line has image the closed interval, retaining its endpoint. -/
theorem eVariationOn_univ_stoppedProcess (X : ℝ≥0 → Ω → ℝ)
    (τ : Ω → WithTop ℝ≥0) (ω : Ω) :
    eVariationOn (fun t ↦ stoppedProcess X τ t ω) univ =
      stoppedValueWithTerminal (eTotalVariationProcess X)
        (fun ω ↦ eVariationOn (X · ω) univ) τ ω := by
  cases ht : τ ω with
  | top =>
      simp only [MeasureTheory.stoppedProcess, ht, min_eq_left le_top,
        WithTop.untopA, WithTop.untopD_coe, stoppedValueWithTerminal_of_top ht]
  | coe T =>
      rw [stoppedValueWithTerminal_of_ne_top (ht ▸ WithTop.coe_ne_top)]
      simp only [MeasureTheory.stoppedProcess, stoppedValue, ht, ← WithTop.coe_min,
        WithTop.untopA, WithTop.untopD_coe, eTotalVariationProcess]
      have him : (fun u : ℝ≥0 ↦ min u T) '' univ = Icc 0 T := by
        ext u
        constructor
        · rintro ⟨v, _, rfl⟩
          exact ⟨bot_le, min_le_right _ _⟩
        · intro hu
          exact ⟨u, mem_univ _, min_eq_left hu.2⟩
      exact (eVariationOn.comp_eq_of_monotoneOn (X · ω) (fun u ↦ min u T)
        (fun _ _ _ _ h ↦ min_le_min_right T h)).trans
        (congrArg (eVariationOn (X · ω)) him)

/-- Stopping cannot increase the extended total variation, even when it is infinite. -/
theorem eVariationOn_univ_stoppedProcess_le (X : ℝ≥0 → Ω → ℝ)
    (τ : Ω → WithTop ℝ≥0) (ω : Ω) :
    eVariationOn (fun t ↦ stoppedProcess X τ t ω) univ ≤
      eVariationOn (X · ω) univ := by
  rw [eVariationOn_univ_stoppedProcess]
  cases ht : τ ω with
  | top => rw [stoppedValueWithTerminal_of_top ht]
  | coe T =>
      rw [stoppedValueWithTerminal_of_ne_top (ht ▸ WithTop.coe_ne_top)]
      simp only [stoppedValue, ht, WithTop.untopA, WithTop.untopD_coe, eTotalVariationProcess]
      exact eVariationOn.mono _ (subset_univ _)

theorem HasFiniteTotalVariationPaths.stoppedProcess
    (hv : HasFiniteTotalVariationPaths X P) (τ : Ω → WithTop ℝ≥0) :
    HasFiniteTotalVariationPaths (stoppedProcess X τ) P := by
  filter_upwards [hv] with ω hω
  exact ne_top_of_le_ne_top hω (eVariationOn_univ_stoppedProcess_le X τ ω)

end ProbabilityTheory
