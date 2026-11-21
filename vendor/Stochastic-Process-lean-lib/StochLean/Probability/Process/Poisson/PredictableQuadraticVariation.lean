/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.Poisson.QuadraticVariation
public import StochLean.Probability.Process.Poisson.SpecialDecomposition
public import StochLean.Probability.Process.Semimartingale.PredictableQuadraticVariation

/-! # Actual Poisson predictable quadratic variation

The existing raw quadratic variations of the real Poisson count and its
compensated process are both the actual count. Its coordinate integrability
and monotone paths establish local integrability of variation, so the sole
predictable-quadratic-variation selector has its actual domain proof.

With future increments independent of the chosen past, the already proved
canonical Poisson decomposition identifies the count's compensator with its
deterministic linear drift. Canonical compensator coherence then identifies
both selected angle processes with that drift. The identities include rate
zero and do not assert independence for arbitrary enlarged filtrations.

At positive rate the compensated process's raw and predictable quadratic
variations are not indistinguishable. Otherwise the compensated count would
vanish, contradicting the existing exact second-moment argument. These are
consumers for a supplied actual Poisson process, not a new sample-space model,
bracket, compensator, or compensated-process definition.
-/

@[expose] public section

open MeasureTheory Filter
open scoped NNReal

namespace ProbabilityTheory.IsPoissonProcess

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
  {F : Filtration ℝ≥0 mΩ} {N : ℝ≥0 → Ω → ℕ} {rate : ℝ≥0}

private theorem locally_integrable_variation_real
    (hN : IsPoissonProcess N rate P) (hF : F.IsUsual P) (ha : Adapted F N) :
    HasLocallyIntegrableVariation (fun t ω ↦ (N t ω : ℝ)) F P := by
  have haR : Adapted F (fun t ω ↦ (N t ω : ℝ)) := fun t ↦
    (continuous_of_discreteTopology : Continuous (fun n : ℕ ↦ (n : ℝ))).measurable.comp (ha t)
  exact hN.hasMonotonePaths_real.hasLocallyIntegrableVariation_of_locally_integrable
    haR hF hN.hasCadlagPaths_real (Locally.of_prop hN.integrable_real)

/-- Both original raw quadratic variations have actual locally integrable
variation, before any candidate predictable angle process is identified. -/
theorem hasLocallyIntegrableVariation_quadraticVariation_real_and_compensated
    (hN : IsPoissonProcess N rate P) (hF : F.IsUsual P) (ha : Adapted F N) :
    HasLocallyIntegrableVariation
      ((hN.isSemimartingale_real hF ha).quadraticVariation hF) F P ∧
    HasLocallyIntegrableVariation
      ((hN.isSemimartingale_compensated hF ha).quadraticVariation hF) F P := by
  have hv := locally_integrable_variation_real hN hF ha
  exact ⟨hv.congr (hN.quadraticVariation_real_eq hF ha).symm,
    hv.congr (hN.quadraticVariation_compensated_eq hF ha).symm⟩

/-- The actual selected angles of both the count and compensated count equal
the linear drift. The rate may be zero; the filtration independence is explicit. -/
theorem predictableQuadraticVariation_real_and_compensated_eq_of_indep_past
    (hN : IsPoissonProcess N rate P) (ha : Adapted F N)
    (hi : ∀ s t, s ≤ t → Indep (F s) (MeasurableSpace.comap
      (fun ω ↦ (N t ω : ℝ) - (N s ω : ℝ)) inferInstance) P)
    (hF : F.IsUsual P) :
    let hQ := hN.hasLocallyIntegrableVariation_quadraticVariation_real_and_compensated hF ha
    Indistinguishable
      ((hN.isSemimartingale_real hF ha).predictableQuadraticVariation hF hQ.1)
      (fun (t : ℝ≥0) (_ : Ω) ↦ (rate : ℝ) * t) P ∧
    Indistinguishable
      ((hN.isSemimartingale_compensated hF ha).predictableQuadraticVariation hF hQ.2)
      (fun (t : ℝ≥0) (_ : Ω) ↦ (rate : ℝ) * t) P := by
  let hQ := hN.hasLocallyIntegrableVariation_quadraticVariation_real_and_compensated hF ha
  let hR := hN.isSemimartingale_real hF ha
  let hC := hN.isSemimartingale_compensated hF ha
  have hvN := locally_integrable_variation_real hN hF ha
  have haN : Adapted F (fun t ω ↦ (N t ω : ℝ)) := fun t ↦
    (continuous_of_discreteTopology : Continuous (fun n : ℕ ↦ (n : ℝ))).measurable.comp (ha t)
  obtain ⟨hS, _, hD⟩ := hN.special_decomposition_of_indep_past ha hi hF
  have hComp : Indistinguishable
      (hvN.predictableCompensator haN hF hN.hasCadlagPaths_real)
      (fun (t : ℝ≥0) (_ : Ω) ↦ (rate : ℝ) * t) P :=
    ((hS.canonicalParts_eq_predictableCompensator hF hvN).2).symm.trans hD
  constructor
  · exact (hQ.1.predictableCompensator_congr hvN (hR.adapted_quadraticVariation hF)
      haN hF (hR.hasCadlagPaths_quadraticVariation hF) hN.hasCadlagPaths_real
      (hN.quadraticVariation_real_eq hF ha)).trans hComp
  · exact (hQ.2.predictableCompensator_congr hvN (hC.adapted_quadraticVariation hF)
      haN hF (hC.hasCadlagPaths_quadraticVariation hF) hN.hasCadlagPaths_real
      (hN.quadraticVariation_compensated_eq hF ha)).trans hComp

/-- At positive rate the compensated Poisson raw bracket is genuinely
different from its selected angle process, by the proved Poisson second moment. -/
theorem quadraticVariation_compensated_ne_predictable_of_pos
    (hN : IsPoissonProcess N rate P) (ha : Adapted F N)
    (hi : ∀ s t, s ≤ t → Indep (F s) (MeasurableSpace.comap
      (fun ω ↦ (N t ω : ℝ) - (N s ω : ℝ)) inferInstance) P)
    (hF : F.IsUsual P) (hrate : 0 < rate) :
    let hQ := hN.hasLocallyIntegrableVariation_quadraticVariation_real_and_compensated hF ha
    ¬ Indistinguishable ((hN.isSemimartingale_compensated hF ha).quadraticVariation hF)
      ((hN.isSemimartingale_compensated hF ha).predictableQuadraticVariation hF hQ.2) P := by
  dsimp only
  intro he
  have hraw := hN.quadraticVariation_compensated_eq hF ha
  have hangle := (hN.predictableQuadraticVariation_real_and_compensated_eq_of_indep_past
    ha hi hF).2
  have hND := hraw.symm.trans (he.trans hangle)
  apply (hN.classical_decompositions_nonunique_of_pos ha hi hF hrate).2.2
  filter_upwards [hND] with ω hω t
  change 0 = (N t ω : ℝ) - (rate : ℝ) * t
  rw [hω t, sub_self]

end ProbabilityTheory.IsPoissonProcess
