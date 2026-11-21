/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.FiniteVariation.CompensatorLocal
public import StochLean.Probability.Process.FiniteVariation.LocallyIntegrableAlgebra
public import StochLean.Probability.Process.LocalMartingale.InitialValue

/-! # Predictable compensators without initial integrability

Subtracting the original initial random value preserves locally integrable
variation and makes the centered initial value exactly zero. The existing
local construction supplies its actual predictable compensator.

The time-constant original initial value is a Protter local martingale by the
existing masked initial-value localization theorem; it need not be integrable.
Adding it back restores the original process without changing the compensator.
The same centering transforms any competing local-martingale remainder, so
the already proved uniqueness is retained. No unmasked Klenke localization,
new selector, or additional initial moment is silently assumed.
-/

@[expose] public section

open MeasureTheory Filter
open scoped NNReal

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
  {F : Filtration ℝ≥0 mΩ} {X : ℝ≥0 → Ω → ℝ}

/-- Every adapted cadlag process of locally integrable variation has a
unique normalized predictable compensator with a local-martingale remainder.
No integrability or zero-value assumption on the original initial value is
required. A competing predictable part need only have finite variation. -/
theorem HasLocallyIntegrableVariation.exists_unique_predictable_compensator
    (hv : HasLocallyIntegrableVariation X F P) (ha : Adapted F X) (hF : F.IsUsual P)
    (hc : HasCadlagPaths X P) :
    ∃ A : ℝ≥0 → Ω → ℝ,
      IsStronglyPredictable F A ∧ (∀ ω, IsCadlagPath (A · ω)) ∧ A 0 = 0 ∧
      HasLocallyIntegrableVariation A F P ∧ IsLocalMartingale (X - A) F P ∧
      ∀ B : ℝ≥0 → Ω → ℝ,
        IsStronglyPredictable F B → HasFiniteVariationPaths B P →
        B 0 =ᵐ[P] 0 → IsLocalMartingale (X - B) F P → Indistinguishable A B P := by
  let I : ℝ≥0 → Ω → ℝ := fun _ ↦ X 0
  let Y := X - I
  have hI : IsContinuousLocalMartingale I F P :=
    isContinuousLocalMartingale_const_initial (ha 0)
  have haI : Adapted F I := hI.1.1
  have hcI : HasCadlagPaths I P := hI.2.hasCadlagPaths
  have hvI : HasLocallyIntegrableVariation I F P :=
    (hasIntegrableVariation_const (P := P) (X 0)).hasLocallyIntegrableVariation
  have hvY : HasLocallyIntegrableVariation Y F P := hv.sub hvI ha haI hF hc hcI
  have haY : Adapted F Y := ha.sub haI
  have hcY : HasCadlagPaths Y P := hc.sub hcI
  have hY0 : Y 0 = 0 := by
    funext ω
    exact sub_self (X 0 ω)
  have hiY0 : Integrable (Y 0) P := by
    rw [hY0]
    exact ⟨aestronglyMeasurable_const, by simp [HasFiniteIntegral]⟩
  obtain ⟨A, hpA, hcA, hA0, hvA, hMY, huniq⟩ :=
    hvY.exists_unique_predictable_compensator_of_integrable_initial haY hF hcY hiY0
  have he : (Y - A) + I = X - A := by
    funext t ω
    change (X t ω - X 0 ω - A t ω) + X 0 ω = X t ω - A t ω
    ring
  have hM : IsLocalMartingale (X - A) F P := he ▸ hMY.add hI.1 hF
  refine ⟨A, hpA, hcA, hA0, hvA, hM, ?_⟩
  intro B hpB hvB hB0 hMB
  have heB : (X - B) - I = Y - B := by
    funext t ω
    change (X t ω - B t ω) - X 0 ω = (X t ω - X 0 ω) - B t ω
    ring
  exact huniq B hpB hvB hB0 (heB ▸ hMB.sub hI.1 hF)

end ProbabilityTheory
