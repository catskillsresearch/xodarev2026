/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.FiniteVariation.LocallyIntegrable
public import StochLean.Probability.Process.Measurability.InitialMask

/-! # Iterated localization of integrable variation

The stable property includes adaptedness and common-event cadlag paths, which
supply the measurability of actual stopped variation. Bare integrable
variation is not asserted to be stable for arbitrary nonadapted processes.

Both levels retain Mathlib's positive-lifetime mask and their original
localizing sequences. The existing stable-property idempotence performs the
diagonal extraction; no additional local predicate or selector is introduced.
Finite measure is needed only for that extraction, not for the stability or
the same-sequence upgrade. Initial values need not vanish or be integrable.
-/

@[expose] public section

open MeasureTheory Set
open scoped NNReal

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
  {F : Filtration ℝ≥0 mΩ} {X : ℝ≥0 → Ω → ℝ}

private theorem adapted_cadlag_masked_stoppedProcess
    (ha : Adapted F X) (hF : F.IsUsual P) (hc : HasCadlagPaths X P)
    {τ : Ω → WithTop ℝ≥0} (hτ : IsStoppingTime F τ) :
    Adapted F (stoppedProcess (fun t ↦ {ω | 0 < τ ω}.indicator (X t)) τ) ∧
      HasCadlagPaths (stoppedProcess (fun t ↦ {ω | 0 < τ ω}.indicator (X t)) τ) P := by
  have hs : MeasurableSet[F 0] {ω | 0 < τ ω} := hτ.measurableSet_gt 0
  have hcMask := hc.indicator {ω | 0 < τ ω}
  exact ⟨((ha.indicator_initial hs).stronglyAdapted.stoppedProcess_of_usual hF
    hcMask.hasRightContinuousPaths hτ).adapted, hcMask.stoppedProcess τ⟩

/-- The adapted cadlag integrable-variation bundle is stable under the native
positive-lifetime masked stopping operation on a usual filtration. -/
theorem isStable_adapted_cadlag_integrableVariation (hF : F.IsUsual P) :
    IsStable F (fun Y ↦ Adapted F Y ∧ HasCadlagPaths Y P ∧
      HasIntegrableVariation Y P) := by
  intro Y hY τ hτ
  have hs := adapted_cadlag_masked_stoppedProcess hY.1 hF hY.2.1 hτ
  exact ⟨hs.1, hs.2,
    (hasIntegrableVariation_stoppedProcess_indicator_pos_iff Y τ).mpr
      (hY.2.2.stoppedProcess hY.1 hF hY.2.1 hτ)⟩

/-- The original localizing sequence already localizes the stable bundle:
adaptedness and cadlag paths are inherited by its actual masked stopped paths. -/
theorem HasLocallyIntegrableVariation.locally_adapted_cadlag_integrableVariation
    (hX : HasLocallyIntegrableVariation X F P) (ha : Adapted F X)
    (hF : F.IsUsual P) (hc : HasCadlagPaths X P) :
    Locally (fun Y ↦ Adapted F Y ∧ HasCadlagPaths Y P ∧
      HasIntegrableVariation Y P) F X P := by
  obtain ⟨τ, hτ, hv⟩ := hX
  refine ⟨τ, hτ, fun n ↦ ?_⟩
  have hs := adapted_cadlag_masked_stoppedProcess ha hF hc (hτ.isStoppingTime n)
  exact ⟨hs.1, hs.2, hv n⟩

/-- Actual local integrable variation can be iterated. The usual adapted
cadlag source supplies the stable bundle required by native idempotence. -/
theorem hasLocallyIntegrableVariation_of_locally [IsFiniteMeasure P]
    (hF : F.IsUsual P) (ha : Adapted F X) (hc : HasCadlagPaths X P)
    (hL : Locally (fun Y ↦ HasLocallyIntegrableVariation Y F P) F X P) :
    HasLocallyIntegrableVariation X F P := by
  let : F.IsRightContinuous := hF.rightContinuous
  have hLL : Locally (fun Y ↦ Locally (fun Z ↦ Adapted F Z ∧
      HasCadlagPaths Z P ∧ HasIntegrableVariation Z P) F Y P) F X P := by
    obtain ⟨τ, hτ, hv⟩ := hL
    refine ⟨τ, hτ, fun n ↦ ?_⟩
    have hs := adapted_cadlag_masked_stoppedProcess ha hF hc (hτ.isStoppingTime n)
    exact (hv n).locally_adapted_cadlag_integrableVariation hs.1 hF hs.2
  have hB := (isStable_adapted_cadlag_integrableVariation hF).locally_locally_iff.mp hLL
  exact hB.mono fun _ hY ↦ hY.2.2

/-- On the usual adapted cadlag domain, locally integrable variation is
unchanged by one further application of the canonical local predicate. -/
theorem locally_hasLocallyIntegrableVariation_iff [IsFiniteMeasure P]
    (hF : F.IsUsual P) (ha : Adapted F X) (hc : HasCadlagPaths X P) :
    Locally (fun Y ↦ HasLocallyIntegrableVariation Y F P) F X P ↔
      HasLocallyIntegrableVariation X F P :=
  ⟨hasLocallyIntegrableVariation_of_locally hF ha hc, fun hX ↦ Locally.of_prop hX⟩

end ProbabilityTheory
