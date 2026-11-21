/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.FiniteVariation.CanonicalCompensator
public import StochLean.Probability.Process.FiniteVariation.RunningJumpCriterion
public import StochLean.Probability.Process.Measurability.RunningSupremumLocalIntegrability
public import StochLean.Probability.Process.Semimartingale.SpecialRunningSupremum

/-! # Local integrability of finite-variation local martingales and special processes

The actual running norm supremum of a native local martingale is locally
integrable. Its running jump supremum is therefore locally integrable as
well, and the existing FV jump criterion supplies actual locally integrable
variation. The same argument applies directly to special semimartingales.

Together with actual compensator existence, this identifies specialness
with locally integrable variation on the adapted cadlag FV domain. All
localizations retain their native positive-lifetime masks. In particular,
no initial moment or product of random integrable envelopes is assumed.
-/

@[expose] public section

open MeasureTheory
open scoped NNReal

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
  {F : Filtration ℝ≥0 mΩ} {X : ℝ≥0 → Ω → ℝ}

/-- A native local martingale with FV paths has actual locally integrable
variation, even when its original initial value is not integrable. -/
theorem IsLocalMartingale.hasLocallyIntegrableVariation_of_finiteVariation
    (hX : IsLocalMartingale X F P) (hF : F.IsUsual P)
    (hv : HasFiniteVariationPaths X P) : HasLocallyIntegrableVariation X F P :=
  hv.hasLocallyIntegrableVariation_of_locally_integrable_runningJumpSupremum
    hX.1 hF hX.2.1
    (hX.1.locally_integrable_runningJumpSupremum_of_denseRunningSupremum hF hX.2.1
      (hX.locally_integrable_denseRunningSupremum hF))

/-- Specialness and actual FV paths suffice for locally integrable variation;
predictability of the original process is not required. -/
theorem IsSpecialSemimartingale.hasLocallyIntegrableVariation_of_finiteVariation
    (hX : IsSpecialSemimartingale X F P) (hF : F.IsUsual P)
    (hv : HasFiniteVariationPaths X P) : HasLocallyIntegrableVariation X F P :=
  hv.hasLocallyIntegrableVariation_of_locally_integrable_runningJumpSupremum
    hX.1 hF hX.2.1 (hX.locally_integrable_runningJumpSupremum hF)

/-- On the adapted cadlag FV domain, specialness is equivalent to actual
locally integrable variation. Both directions retain arbitrary initial values. -/
theorem HasFiniteVariationPaths.isSpecialSemimartingale_iff_hasLocallyIntegrableVariation
    (hv : HasFiniteVariationPaths X P) (ha : Adapted F X) (hF : F.IsUsual P)
    (hc : HasCadlagPaths X P) :
    IsSpecialSemimartingale X F P ↔ HasLocallyIntegrableVariation X F P :=
  ⟨fun hX ↦ hX.hasLocallyIntegrableVariation_of_finiteVariation hF hv,
    fun hX ↦ hX.isSpecialSemimartingale ha hF hc⟩

end ProbabilityTheory
