/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.Counting.KernelHazardUniformIntegrability
public import StochLean.Probability.Process.Counting.KernelHazardPaths
public import StochLean.ForMathlib.MeasureTheory.Function.UniformIntegrablePullback
public import Mathlib.Probability.Kernel.CondDistrib

/-! # Actual conditional-lifetime hazards on the original sample space

The lifetime law conditional on a measurable history is Mathlib's existing
`condDistrib`. Its composition product with the actual history law is the
joint pushforward of the original history and lifetime. Pullback along this
genuine measurable pair map transfers integrability, the positive-occurrence
mean, global uniform integrability and common-event path regularity to the
original space.

Neither the original sample space nor the history space is assumed to be
standard Borel. Only the fixed lifetime target has that structure, as required
by the native conditional-distribution construction. The map need not be
injective; integral transport uses the actual measurable-pushforward theorem.

There is no filtration, martingale or predictability conclusion here, and no
assumption that history is exposed at time zero. Initial atoms and infinite
lifetimes are retained. The extended hazard is genuinely finite at every
finite observation on one common event, rather than by an exchange of
uncountably many coordinatewise almost-everywhere statements. No new kernel,
hazard, terminal-value or process selector is introduced.
-/

@[expose] public section

open MeasureTheory Set
open scoped NNReal ENNReal ProbabilityTheory

namespace ProbabilityTheory

private theorem standardBorel_conditionalLifetime : StandardBorelSpace (WithTop ℝ≥0) :=
  inferInstanceAs (StandardBorelSpace ℝ≥0∞)

attribute [local instance] standardBorel_conditionalLifetime

variable {Ω K : Type*} {mΩ : MeasurableSpace Ω} {mK : MeasurableSpace K}
  {P : Measure Ω} [IsProbabilityMeasure P]
  {H : Ω → K} {τ : Ω → WithTop ℝ≥0}

private theorem measurePreserving_history_lifetime_condDistrib
    (hH : Measurable H) (hτ : Measurable τ) :
    MeasurePreserving (fun ω ↦ (H ω, τ ω)) P
      ((P.map H) ⊗ₘ condDistrib τ H P) :=
  ⟨hH.prodMk hτ, (compProd_map_condDistrib hτ.aemeasurable).symm⟩

/-- The actual real hazard of the conditional lifetime is integrable on
the original sample space and has the original positive-occurrence mean. -/
theorem integrable_stopped_eCumulativeHazard_condDistrib
    (hH : Measurable H) (hτ : Measurable τ) (t : ℝ≥0) :
    let : StandardBorelSpace (WithTop ℝ≥0) := inferInstanceAs (StandardBorelSpace ℝ≥0∞)
    let κ := condDistrib τ H P
    Integrable (stoppedProcess
      (fun r ω ↦ (eCumulativeHazard (κ (H ω)) r).toReal) τ t) P ∧
      (∫ ω, stoppedProcess
        (fun r v ↦ (eCumulativeHazard (κ (H v)) r).toReal) τ t ω ∂P) =
        P.real {ω | 0 < τ ω ∧ τ ω ≤ (t : WithTop ℝ≥0)} := by
  let κ := condDistrib τ H P
  let φ : Ω → K × WithTop ℝ≥0 := fun ω ↦ (H ω, τ ω)
  let A : K × WithTop ℝ≥0 → ℝ := fun p ↦ stoppedProcess
    (fun r (_ : WithTop ℝ≥0) ↦ (eCumulativeHazard (κ p.1) r).toReal) id t p.2
  have hMP : MeasurePreserving φ P ((P.map H) ⊗ₘ κ) :=
    measurePreserving_history_lifetime_condDistrib hH hτ
  obtain ⟨hi, he⟩ := integrable_stoppedProcess_eCumulativeHazard_compProd (P.map H) κ t
  change Integrable (A ∘ φ) P ∧ (∫ ω, A (φ ω) ∂P) = _
  refine ⟨hMP.integrable_comp_of_integrable hi, ?_⟩
  have hm : AEStronglyMeasurable A (P.map φ) := by
    rw [hMP.map_eq]
    exact hi.aestronglyMeasurable
  calc
    (∫ ω, A (φ ω) ∂P) = ∫ p, A p ∂((P.map H) ⊗ₘ κ) := by
      rw [← hMP.map_eq]
      exact (integral_map hMP.measurable.aemeasurable hm).symm
    _ = ((P.map H) ⊗ₘ κ).real
        {p : K × WithTop ℝ≥0 | 0 < p.2 ∧ p.2 ≤ (t : WithTop ℝ≥0)} := he
    _ = P.real {ω | 0 < τ ω ∧ τ ω ≤ (t : WithTop ℝ≥0)} := by
      rw [← hMP.map_eq]
      exact map_measureReal_apply hMP.measurable
        (show MeasurableSet
          {p : K × WithTop ℝ≥0 | 0 < p.2 ∧ p.2 ≤ (t : WithTop ℝ≥0)} from
          (measurableSet_lt measurable_const measurable_snd).inter
            (measurableSet_le measurable_snd measurable_const))

/-- The actual closed count minus its conditional-lifetime stopped hazard
is uniformly integrable over the whole nonnegative halfline on the original
sample space, without assuming any martingale or filtration structure. -/
theorem uniformIntegrable_singleJump_sub_hazard_condDistrib
    (hH : Measurable H) (hτ : Measurable τ) :
    let : StandardBorelSpace (WithTop ℝ≥0) := inferInstanceAs (StandardBorelSpace ℝ≥0∞)
    let κ := condDistrib τ H P
    UniformIntegrable (fun (t : ℝ≥0) ω ↦
      (if τ ω ≤ (t : WithTop ℝ≥0) then (1 : ℝ) else 0) -
      stoppedProcess (fun r v ↦ (eCumulativeHazard (κ (H v)) r).toReal) τ t ω) 1 P := by
  let κ := condDistrib τ H P
  have hMP := measurePreserving_history_lifetime_condDistrib (P := P) hH hτ
  have hu := UniformIntegrable.comp_measurePreserving
    (uniformIntegrable_singleJump_sub_hazard_compProd (P.map H) κ) hMP le_rfl (by simp)
  simpa only [κ, Function.comp_def, stoppedProcess, id_eq] using hu

/-- On one common event, the actual conditional-lifetime hazard is finite
at all finite observations and has monotone cadlag paths. No standard Borel
condition on the original sample or history space is needed. -/
theorem ae_stopped_eCumulativeHazard_condDistrib_paths
    (hH : Measurable H) (hτ : Measurable τ) :
    let : StandardBorelSpace (WithTop ℝ≥0) := inferInstanceAs (StandardBorelSpace ℝ≥0∞)
    let κ := condDistrib τ H P
    ∀ᵐ ω ∂P,
      (∀ t : ℝ≥0, stoppedProcess
        (fun r v ↦ eCumulativeHazard (κ (H v)) r) τ t ω ≠ ∞) ∧
      Monotone (fun t ↦ stoppedProcess
        (fun r v ↦ (eCumulativeHazard (κ (H v)) r).toReal) τ t ω) ∧
      IsCadlagPath (fun t ↦ stoppedProcess
        (fun r v ↦ (eCumulativeHazard (κ (H v)) r).toReal) τ t ω) := by
  let κ := condDistrib τ H P
  have he := ae_compProd_stopped_eCumulativeHazard_paths (P.map H) κ
  change ∀ᵐ p ∂((P.map H) ⊗ₘ condDistrib τ H P), _ at he
  rw [compProd_map_condDistrib hτ.aemeasurable] at he
  simpa only [κ, stoppedProcess, id_eq] using
    (ae_of_ae_map (μ := P) (hH.prodMk hτ).aemeasurable he)

end ProbabilityTheory
