/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Martingale.Doob.ContinuousLocalization
public import StochLean.Probability.Martingale.Doob.ContinuousClassDLocalization

/-! # Continuous Doob decomposition for Class D processes with bounded jumps

The bounded theorem constructs the compensators of the actual capped norm
exits, and uniqueness supplies their stopped consistency. The common Class D
localization theorem then constructs and closes the global continuous
compensator, including its actual integrable whole-half-line terminal.

This is the bounded-jump-norm Class D extension of Protter III.10, not the
arbitrary-jump extension or the predictable-compensator theorem III.11.
-/

@[expose] public section

open ProbabilityTheory Filter
open scoped NNReal ENNReal Topology

namespace MeasureTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
  [IsProbabilityMeasure P] {F : Filtration ℝ≥0 mΩ}
  {X : ℝ≥0 → Ω → ℝ} {c : ℝ}

/-- The bounded-jump Class D case of the continuous Doob decomposition.
All local compensators, their consistency, the global compensator, its
integrable terminal variable, and the true UI martingale are constructed
from the original process. The increasing part is exactly zero at time zero. -/
theorem Supermartingale.exists_continuous_doob_decomposition_of_classD_of_jump_bound
    (hX : Supermartingale X F P) (hXD : IsClassD X F P) (hF : F.IsUsual P)
    (hc : HasCadlagPaths X P) (hJ : HasTotallyInaccessibleJumps F X P)
    (h0 : X 0 =ᵐ[P] 0) (hb : 0 ≤ c)
    (hj : ∀ᵐ ω ∂P, ∀ t : ℝ≥0, 0 < t → ‖jumpProcess X t ω‖ ≤ c) :
    ∃ (A : ℝ≥0 → Ω → ℝ) (Z : Ω → ℝ),
      Adapted F A ∧ IsStronglyPredictable F A ∧ (∀ ω, Continuous (A · ω)) ∧
      A 0 = 0 ∧ HasMonotonePaths A P ∧ HasFiniteVariationPaths A P ∧
      IsClassD A F P ∧ Martingale (X + A) F P ∧ HasCadlagPaths (X + A) P ∧
      UniformIntegrable (X + A) 1 P ∧ Integrable Z P ∧
      (∀ᵐ ω ∂P, ∀ t, 0 ≤ A t ω ∧ A t ω ≤ Z ω) ∧
      (∀ᵐ ω ∂P, Tendsto (fun t : ℝ≥0 ↦ A t ω) atTop (𝓝 (Z ω))) ∧
      Tendsto (fun t : ℝ≥0 ↦ eLpNorm (A t - Z) 1 P) atTop (𝓝 0) := by
  have hτ : IsPreLocalizingSequence F (cappedNormExitSequence X) P :=
    (hX.stronglyAdapted.adapted.isLocalizingSequence_cappedNormExitSequence hF hc).1
  obtain ⟨B, _, hdata, hcons⟩ :=
    hX.exists_consistent_continuous_doob_localization_of_jump_bound hF hc hJ h0 hb hj
  have hd (n : ℕ) : Adapted F (B n) ∧ (∀ ω, Continuous (B n · ω)) ∧ B n 0 = 0 ∧
      HasMonotonePaths (B n) P ∧
      Martingale (stoppedProcess X (cappedNormExitSequence X n) + B n) F P := by
    obtain ⟨ha, _, hcont, hz, hm, _, _, _, hM, _, _, _, _⟩ := hdata n
    exact ⟨ha, hcont, hz, hm, hM⟩
  exact exists_continuous_doob_decomposition_of_consistent_classD_localization
    hX.stronglyAdapted.adapted hXD hF hc h0 hτ
    (fun n ↦ (hd n).1) (fun n ↦ (hd n).2.1) (fun n ↦ (hd n).2.2.1)
    (fun n ↦ (hd n).2.2.2.1) (fun n ↦ (hd n).2.2.2.2) hcons

end MeasureTheory
