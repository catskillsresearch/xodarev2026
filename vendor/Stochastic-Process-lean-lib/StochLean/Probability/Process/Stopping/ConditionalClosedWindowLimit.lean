/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.Stopping.ConditionalWindowLimit

/-! # Uniform conditional probabilities of small stopping windows

Protter III.10, Lemma 2: for a totally inaccessible time, consistent right-continuous
versions of the closed-window conditional probabilities have running suprema tending to
zero in probability on each compact time interval. The fixed-time endpoint bridge below
does not change the strict lower endpoint in the bounded random-time sampling theorem.
-/

@[expose] public section

open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
  {F : Filtration ℝ≥0 mΩ} {τ : Ω → WithTop ℝ≥0}

/-- Only deterministic lower endpoints may be changed using absence of finite atoms.
This is not a random-time closed-window sampling identity. -/
theorem IsTotallyInaccessibleStoppingTime.condExp_closed_window_eq_open
    (hτ : IsTotallyInaccessibleStoppingTime F τ P) (t δ : ℝ≥0) :
    P[{ω | (t : WithTop ℝ≥0) ≤ τ ω ∧ τ ω ≤ ((t + δ : ℝ≥0) : WithTop ℝ≥0)}.indicator
      (fun _ ↦ (1 : ℝ)) | F t] =ᵐ[P]
    P[{ω | (t : WithTop ℝ≥0) < τ ω ∧ τ ω ≤ ((t + δ : ℝ≥0) : WithTop ℝ≥0)}.indicator
      (fun _ ↦ (1 : ℝ)) | F t] := by
  apply condExp_congr_ae
  have hn : ∀ᵐ ω ∂P, τ ω ≠ (t : WithTop ℝ≥0) := by
    rw [ae_iff]
    simpa only [not_not] using hτ.measure_eq_const t
  filter_upwards [hn] with ω hω
  have hl : (t : WithTop ℝ≥0) < τ ω ↔ (t : WithTop ℝ≥0) ≤ τ ω :=
    lt_iff_le_and_ne.trans (and_iff_left hω.symm)
  simp only [indicator_apply, mem_ofPred_eq, hl]

variable [IsFiniteMeasure P] {R : ℝ≥0 → ℝ≥0 → Ω → ℝ}

theorem IsTotallyInaccessibleStoppingTime.tendsto_closed_window_supremum
    (hτ : IsTotallyInaccessibleStoppingTime F τ P) (hF : F.IsUsual P)
    (hrR : ∀ δ, HasRightContinuousPaths (R δ) P)
    (heR : ∀ δ (t : ℝ≥0), R δ t =ᵐ[P]
      P[{ω | (t : WithTop ℝ≥0) ≤ τ ω ∧ τ ω ≤ ((t + δ : ℝ≥0) : WithTop ℝ≥0)}.indicator
        (fun _ ↦ (1 : ℝ)) | F t]) (ν : ℝ≥0) {a : ℝ} (ha : 0 < a) :
    Tendsto (fun δ ↦ P.real {ω | ENNReal.ofReal a < denseRunningSupremum (R δ) ν ω})
      (𝓝 0) (𝓝 0) :=
  hτ.tendsto_conditional_window_supremum hF hrR
    (fun δ t ↦ (heR δ t).trans (hτ.condExp_closed_window_eq_open t δ)) ν ha

theorem IsTotallyInaccessibleStoppingTime.tendstoInMeasure_closed_window_supremum
    (hτ : IsTotallyInaccessibleStoppingTime F τ P) (hF : F.IsUsual P)
    (hrR : ∀ δ, HasRightContinuousPaths (R δ) P)
    (heR : ∀ δ (t : ℝ≥0), R δ t =ᵐ[P]
      P[{ω | (t : WithTop ℝ≥0) ≤ τ ω ∧ τ ω ≤ ((t + δ : ℝ≥0) : WithTop ℝ≥0)}.indicator
        (fun _ ↦ (1 : ℝ)) | F t]) (ν : ℝ≥0) :
    TendstoInMeasure P (fun δ ω ↦ (denseRunningSupremum (R δ) ν ω).toReal) (𝓝 0)
      (fun _ ↦ (0 : ℝ)) :=
  hτ.tendstoInMeasure_conditional_window_supremum hF hrR
    (fun δ t ↦ (heR δ t).trans (hτ.condExp_closed_window_eq_open t δ)) ν

/-- The versions and their convergence are constructed from total inaccessibility and
the usual conditions. Uniform convergence is not supplied as an input hypothesis. -/
theorem IsTotallyInaccessibleStoppingTime.exists_conditional_closed_windows_tendstoInMeasure
    (hτ : IsTotallyInaccessibleStoppingTime F τ P) (hF : F.IsUsual P) :
    ∃ R : ℝ≥0 → ℝ≥0 → Ω → ℝ,
      (∀ δ, StronglyAdapted F (R δ) ∧ HasCadlagPaths (R δ) P) ∧
      (∀ δ (t : ℝ≥0), R δ t =ᵐ[P]
        P[{ω | (t : WithTop ℝ≥0) ≤ τ ω ∧ τ ω ≤ ((t + δ : ℝ≥0) : WithTop ℝ≥0)}.indicator
          (fun _ ↦ (1 : ℝ)) | F t]) ∧
      (∀ δ, ∀ᵐ ω ∂P, ∀ t : ℝ≥0, 0 ≤ R δ t ω ∧ R δ t ω ≤ 1 ∧
        (τ ω ≤ (t : WithTop ℝ≥0) → R δ t ω = 0)) ∧
      ∀ ν : ℝ≥0, TendstoInMeasure P
        (fun δ ω ↦ (denseRunningSupremum (R δ) ν ω).toReal) (𝓝 0) (fun _ ↦ (0 : ℝ)) := by
  choose R ha hc he hb using fun δ ↦ exists_cadlag_conditional_closed_window hτ hF δ
  exact ⟨R, fun δ ↦ ⟨ha δ, hc δ⟩, he, hb,
    fun ν ↦ hτ.tendstoInMeasure_closed_window_supremum hF
      (fun δ ↦ (hc δ).hasRightContinuousPaths) he ν⟩

end ProbabilityTheory
