/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Martingale.Convergence.ContinuousClosingProjection
public import StochLean.Probability.Process.Filtration.Terminal
public import StochLean.Probability.Process.Stopping.TerminalValue

/-! # The UI martingale on the extended time interval

The existing terminal-valued stopping owner supplies the process at constant
extended times. Its terminal sigma-field is the supremum of the finite-time
filtration. UI is equivalent to existence of an actual integrable limit for
which this extended process is a martingale (Protter I.13).
-/

@[expose] public section

open ProbabilityTheory Filter
open scoped NNReal ENNReal Topology

namespace MeasureTheory.Martingale

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsFiniteMeasure P]
  {F : Filtration ℝ≥0 mΩ} {X : ℝ≥0 → Ω → ℝ} {Z : Ω → ℝ}

theorem withTerminal_of_integrable_closing (hX : Martingale X F P)
    (hZ : Integrable Z P) (hm : StronglyMeasurable[⨆ t, F t] Z)
    (hclose : ∀ t, X t =ᵐ[P] P[Z | F t]) :
    Martingale (fun t : WithTop ℝ≥0 ↦ stoppedValueWithTerminal X Z (fun _ ↦ t))
      F.withTerminal P := by
  let U (t : WithTop ℝ≥0) := stoppedValueWithTerminal X Z (fun _ ↦ t)
  have hU : StronglyAdapted F.withTerminal U := by
    intro t
    cases t using WithTop.recTopCoe with
    | top =>
      change StronglyMeasurable[⨆ t, F t] (U ⊤)
      simpa only [U, stoppedValueWithTerminal_top] using hm
    | coe t =>
      change StronglyMeasurable[F t] (U (t : WithTop ℝ≥0))
      simpa only [U, stoppedValueWithTerminal_coe] using hX.stronglyAdapted t
  have hC (t : WithTop ℝ≥0) : U t =ᵐ[P] P[Z | F.withTerminal t] := by
    cases t using WithTop.recTopCoe with
    | top =>
      simp only [U, stoppedValueWithTerminal_top, Filtration.withTerminal_top,
        condExp_of_stronglyMeasurable (iSup_le F.le) hm hZ]
      exact EventuallyEq.rfl
    | coe t =>
      simpa only [U, stoppedValueWithTerminal_coe, Filtration.withTerminal_coe] using hclose t
  refine ⟨hU, fun i j hij ↦ ?_⟩
  exact (condExp_congr_ae (hC j)).trans
    ((condExp_condExp_of_le (F.withTerminal.mono hij) (F.withTerminal.le j)).trans (hC i).symm)

omit [IsFiniteMeasure P] in
theorem integrable_closing_of_withTerminal
    (hU : Martingale (fun t : WithTop ℝ≥0 ↦ stoppedValueWithTerminal X Z (fun _ ↦ t))
      F.withTerminal P) :
    StronglyMeasurable[⨆ t, F t] Z ∧ Integrable Z P ∧ ∀ t, X t =ᵐ[P] P[Z | F t] := by
  refine ⟨?_, ?_, fun t ↦ ?_⟩
  · have hm := hU.stronglyAdapted ⊤
    change StronglyMeasurable[⨆ t, F t] (stoppedValueWithTerminal X Z (fun _ ↦ ⊤)) at hm
    simpa only [stoppedValueWithTerminal_top] using hm
  · simpa only [stoppedValueWithTerminal_top] using hU.integrable ⊤
  · simpa only [stoppedValueWithTerminal_coe, stoppedValueWithTerminal_top,
      Filtration.withTerminal_coe] using
        (hU.condExp_ae_eq (i := (t : WithTop ℝ≥0)) (j := ⊤) le_top).symm

/-- The actual extended-index martingale assertion of Protter I.13. The
terminal representative is measurable for the terminal sigma-field, and
finite-time values are unchanged, including the original initial value. -/
theorem uniformIntegrable_iff_exists_martingale_withTerminal
    (hX : Martingale X F P) (hc : HasRightContinuousPaths X P) :
    UniformIntegrable X 1 P ↔ ∃ Z : Ω → ℝ, Integrable Z P ∧
      (∀ᵐ ω ∂P, Tendsto (fun t : ℝ≥0 ↦ X t ω) atTop (𝓝 (Z ω))) ∧
      Martingale (fun t : WithTop ℝ≥0 ↦ stoppedValueWithTerminal X Z (fun _ ↦ t))
        F.withTerminal P := by
  constructor
  · intro hu
    obtain ⟨Y, hY, hclose⟩ := hX.exists_integrable_closing hu
    let Z := P[Y | ⨆ t, F t]
    obtain ⟨hlim, _, hZclose⟩ := hX.tendsto_terminalProjection_of_integrable_closing hc hY hclose
    exact ⟨Z, integrable_condExp, hlim,
      hX.withTerminal_of_integrable_closing integrable_condExp stronglyMeasurable_condExp hZclose⟩
  · rintro ⟨Z, _, _, hU⟩
    obtain ⟨_, hZ, hclose⟩ := hU.integrable_closing_of_withTerminal
    exact uniformIntegrable_of_integrable_closing hZ hclose

end MeasureTheory.Martingale
