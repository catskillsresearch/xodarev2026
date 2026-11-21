/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.FiniteVariation.TerminalLimit
public import StochLean.Probability.Process.FiniteVariation.Integrable

/-! # Terminal limits from integrable whole-half-line variation

The actual full-path variation supplies the domination required by the
existing Jordan terminal construction. Its finiteness is supplied by the
integrable-variation predicate before any real conversion is used. There
is no additional domination variable or new terminal selector.

An integrable initial value remains a separate hypothesis. Class D and
integrability at deterministic or finite stopping times are consumers of
the same terminal theorem, not independent closure arguments.
-/

@[expose] public section

open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsFiniteMeasure P]
  {F : Filtration ℝ≥0 mΩ} {X : ℝ≥0 → Ω → ℝ}

/-- The canonical integrable-variation assumption constructs the actual
integrable terminal on the entire time half-line. Both path and terminal
norms retain the initial-value term in their common variation bound. -/
theorem HasIntegrableVariation.exists_integrable_terminal
    (hv : HasIntegrableVariation X P) (ha : Adapted F X) (hF : F.IsUsual P)
    (hc : HasCadlagPaths X P) (hi0 : Integrable (X 0) P) :
    ∃ Z : Ω → ℝ, Integrable Z P ∧
      (∀ᵐ ω ∂P, Tendsto (fun t : ℝ≥0 ↦ X t ω) atTop (𝓝 (Z ω))) ∧
      Tendsto (fun t : ℝ≥0 ↦ eLpNorm (X t - Z) 1 P) atTop (𝓝 0) ∧
      IsClassD X F P ∧
      (∀ᵐ ω ∂P, ∀ t, ‖X t ω‖ ≤ ‖X 0 ω‖ + (eVariationOn (X · ω) univ).toReal) ∧
      ∀ᵐ ω ∂P, ‖Z ω‖ ≤ ‖X 0 ω‖ + (eVariationOn (X · ω) univ).toReal :=
  hv.hasFiniteVariationPaths.exists_integrable_terminal_of_totalVariation_le ha hF hc hi0
    hv.integrable_eVariationOn_toReal hv.ae_forall_totalVariationProcess_le

/-- Integrable variation together with an integrable initial value gives
Class D under the usual adapted cadlag hypotheses. -/
theorem HasIntegrableVariation.isClassD
    (hv : HasIntegrableVariation X P) (ha : Adapted F X) (hF : F.IsUsual P)
    (hc : HasCadlagPaths X P) (hi0 : Integrable (X 0) P) : IsClassD X F P := by
  obtain ⟨_, _, _, _, hD, _, _⟩ := hv.exists_integrable_terminal ha hF hc hi0
  exact hD

/-- Deterministic-time integrability is inherited from the actual Class D
conclusion and still requires the original initial value to be integrable. -/
theorem HasIntegrableVariation.integrable
    (hv : HasIntegrableVariation X P) (ha : Adapted F X) (hF : F.IsUsual P)
    (hc : HasCadlagPaths X P) (hi0 : Integrable (X 0) P) (t : ℝ≥0) :
    Integrable (X t) P :=
  (hv.isClassD ha hF hc hi0).integrable t

/-- Every everywhere-finite stopping value is integrable, without a
deterministic bound on that stopping time. -/
theorem HasIntegrableVariation.integrable_finiteStoppingTime_value
    (hv : HasIntegrableVariation X P) (ha : Adapted F X) (hF : F.IsUsual P)
    (hc : HasCadlagPaths X P) (hi0 : Integrable (X 0) P) (τ : FiniteStoppingTime F) :
    Integrable (fun ω ↦ X (τ ω) ω) P :=
  (hv.isClassD ha hF hc hi0).integrable_finiteStoppingTime_value τ

end ProbabilityTheory
