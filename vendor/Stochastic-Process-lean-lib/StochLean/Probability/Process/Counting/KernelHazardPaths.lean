/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.Counting.HazardPathRegularity
public import Mathlib.Probability.Kernel.Composition.MeasureCompProd

/-! # Joint common-event regularity for a kernel-valued lifetime hazard

The actual closed-survival positivity event is jointly measurable in the
kernel parameter and lifetime. Its fiber sections have full measure, so
the genuine composition-product law gives it full measure as well.

On this one event the existing pointwise hazard theorem gives finite
extended values at all finite observations, monotonicity and cadlag paths.
This does not exchange uncountably many coordinatewise almost-everywhere
statements or assume that an arbitrary family of fiber path events is
measurable. No hazard or path version is selected again, and initial,
terminal and infinite lifetime atoms remain allowed.
-/

@[expose] public section

open MeasureTheory Set
open scoped NNReal ENNReal ProbabilityTheory

namespace ProbabilityTheory

variable {H : Type*} {mH : MeasurableSpace H}

/-- The original closed survival is positive on a jointly measurable
full-measure event under the actual history/lifetime composition product. -/
theorem ae_compProd_pos_lifetime_survival (η : Measure H) [SFinite η]
    (κ : Kernel H (WithTop ℝ≥0)) [IsSFiniteKernel κ] :
    ∀ᵐ p : H × WithTop ℝ≥0 ∂(η ⊗ₘ κ), 0 < κ p.1 (Ici p.2) := by
  have htail : Measurable (fun p : H × WithTop ℝ≥0 ↦ κ p.1 (Ici p.2)) := by
    have hs : MeasurableSet
        {q : (H × WithTop ℝ≥0) × WithTop ℝ≥0 | q.1.2 ≤ q.2} :=
      measurableSet_le measurable_fst.snd measurable_snd
    exact Kernel.measurable_kernel_prodMk_left
      (κ := κ.comap (Prod.fst : H × WithTop ℝ≥0 → H) measurable_fst) hs
  apply Measure.ae_compProd_of_ae_ae (measurableSet_lt measurable_const htail)
  exact ae_of_all η fun h ↦ ae_pos_measure_Ici (κ h)

/-- For a finite lifetime kernel, the original stopped hazard has finite
extended values at every finite time and monotone cadlag paths, all on
one common event of the actual joint law. -/
theorem ae_compProd_stopped_eCumulativeHazard_paths (η : Measure H) [SFinite η]
    (κ : Kernel H (WithTop ℝ≥0)) [IsFiniteKernel κ] :
    ∀ᵐ p : H × WithTop ℝ≥0 ∂(η ⊗ₘ κ),
      (∀ t : ℝ≥0, stoppedProcess
        (fun r (_ : WithTop ℝ≥0) ↦ eCumulativeHazard (κ p.1) r) id t p.2 ≠ ∞) ∧
      Monotone (fun t ↦ stoppedProcess
        (fun r (_ : WithTop ℝ≥0) ↦ (eCumulativeHazard (κ p.1) r).toReal) id t p.2) ∧
      IsCadlagPath (fun t ↦ stoppedProcess
        (fun r (_ : WithTop ℝ≥0) ↦ (eCumulativeHazard (κ p.1) r).toReal) id t p.2) := by
  filter_upwards [ae_compProd_pos_lifetime_survival η κ] with p hp
  exact stopped_eCumulativeHazard_paths_of_positive_survival (κ p.1) p.2 hp

end ProbabilityTheory
