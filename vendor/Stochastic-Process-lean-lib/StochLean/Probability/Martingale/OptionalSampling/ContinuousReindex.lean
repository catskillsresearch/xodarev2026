/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Martingale.OptionalSampling.ContinuousLp
public import StochLean.Probability.Martingale.OptionalSampling.ContinuousUnbounded
public import StochLean.Probability.Process.Filtration.StoppingTimeReindex

/-! # Martingales sampled on ordered bounded stopping-time families

Each stopping time may have its own deterministic bound. This produces the genuine sampled
filtration, in contrast to the distinct theorem that stopping preserves the original filtration.
-/

@[expose] public section

open ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology

namespace MeasureTheory.Martingale

variable {Ω ι : Type*} {mΩ : MeasurableSpace Ω} [Preorder ι]
  {F : Filtration ℝ≥0 mΩ} {P : Measure Ω} {X : ℝ≥0 → Ω → ℝ}
  [IsFiniteMeasure P] [SigmaFiniteFiltration P F]

theorem stoppingTimeReindex_of_bounded_usual (hX : Martingale X F P)
    (hF : F.IsUsual P) (hr : HasRightContinuousPaths X P)
    (τ : ι → Ω → WithTop ℝ≥0) (hτ : ∀ i, IsStoppingTime F (τ i)) (hmono : Monotone τ)
    (hbound : ∀ i, ∃ T : ℝ≥0, ∀ ω, τ i ω ≤ T) :
    Martingale (fun i ↦ stoppedValue X (τ i)) (F.stoppingTimeReindex τ hτ hmono) P := by
  refine ⟨?_, fun i j hij ↦ ?_⟩
  · intro i
    exact (hX.stronglyAdapted.measurable_stoppedValue_of_usual hF hr (hτ i)).stronglyMeasurable
  · obtain ⟨T, hT⟩ := hbound j
    exact (hX.stoppedValue_ae_eq_condExp_of_bounded_le_usual hF hr (hτ i) (hτ j)
      (hmono hij) hT).symm

omit [SigmaFiniteFiltration P F] in
/-- UI permits individually unbounded, AE-finite sampling times in the original stopped
sigma-fields. This applies to all endpoints of a source finite stopping partition. -/
theorem stoppingTimeReindex_of_ae_finite_usual (hX : Martingale X F P)
    (hu : UniformIntegrable X 1 P) (hF : F.IsUsual P) (hr : HasRightContinuousPaths X P)
    (τ : ι → Ω → WithTop ℝ≥0) (hτ : ∀ i, IsStoppingTime F (τ i)) (hmono : Monotone τ)
    (hfinite : ∀ i, ∀ᵐ ω ∂P, τ i ω ≠ ⊤) :
    Martingale (fun i ↦ stoppedValue X (τ i)) (F.stoppingTimeReindex τ hτ hmono) P := by
  refine ⟨?_, fun i j hij ↦ ?_⟩
  · intro i
    exact (hX.stronglyAdapted.measurable_stoppedValue_of_usual hF hr (hτ i)).stronglyMeasurable
  · exact (hX.stoppedValue_ae_eq_condExp_of_ae_finite_usual hu hF hr (hτ i) (hτ j)
      (ae_of_all _ (hmono hij)) (hfinite j)).symm

end MeasureTheory.Martingale
