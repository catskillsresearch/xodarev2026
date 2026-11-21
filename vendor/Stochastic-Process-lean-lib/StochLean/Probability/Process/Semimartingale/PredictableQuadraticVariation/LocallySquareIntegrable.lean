/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.Semimartingale.PredictableQuadraticVariation.LocalMartingale
public import StochLean.Probability.Process.Semimartingale.QuadraticVariation.Moments
public import StochLean.Probability.Process.Semimartingale.QuadraticVariation.Stopping
public import StochLean.Probability.Process.Semimartingale.InitialMask
public import StochLean.Probability.Process.UCP.InitialMask

/-! # Actual predictable quadratic variation of native locally-L2 martingales

The native local-square-integrability witness consists of square-integrable
martingales stopped after the positive-lifetime initial event mask. The raw
quadratic variation commutes with that mask, as proved from its actual
square-sum UCP limit, and with stopping. Thus the existing finite-time L2
moment theorem makes precisely the native masked stopped raw brackets
integrable. Monotonicity then supplies locally integrable variation.

The resulting angle process is the existing canonical compensator on this
proved domain, not a new selector. No square-integrability or zero assumption
is made on the original initial value: raw quadratic variation starts at its
square, while the predictable quadratic variation starts exactly at zero.
-/

@[expose] public section

open MeasureTheory Filter Set
open scoped NNReal

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
  {F : Filtration ℝ≥0 mΩ} {M : ℝ≥0 → Ω → ℝ}

private theorem quadraticVariation_indicator_initial
    (hM : IsSemimartingale M F P) (hF : F.IsUsual P)
    {s : Set Ω} (hs : MeasurableSet[F 0] s) :
    Indistinguishable ((hM.indicator_initial hs).quadraticVariation hF)
      (fun t ↦ s.indicator (hM.quadraticVariation hF t)) P := by
  let π : ℕ → StoppingTimePartition F := fun n ↦ StoppingTimePartition.deterministic F
    ((StochLean.LocallyFinitePartition.dyadic n).restrict n)
  have hπ : StoppingTimePartition.IsTendingToIdentity π P :=
    StoppingTimePartition.isTendingToIdentity_of_klenke
      StochLean.LocallyFinitePartition.dyadic_admissible tendsto_natCast_atTop_atTop
  have hu : TendstoUCP P
      (fun n ↦ (π n).quadraticVariationSumProcess (fun t ↦ s.indicator (M t))) atTop
      (fun t ↦ s.indicator (hM.quadraticVariation hF t)) := by
    apply ((hM.tendstoUCP_quadraticVariationSumProcess hF hπ).indicator s).congr_left
    intro n
    exact Eventually.of_forall fun ω t ↦ by
      by_cases hω : ω ∈ s <;>
        simp [StoppingTimePartition.quadraticVariationSumProcess,
          StochLean.quadraticVariationSum, StochLean.TimePartition.increment, hω]
  have huM := (hM.indicator_initial hs).tendstoUCP_quadraticVariationSumProcess hF hπ
  exact huM.indistinguishable_unique hu
    ((hM.indicator_initial hs).hasCadlagPaths_quadraticVariation hF).hasRightContinuousPaths
    (((hM.hasCadlagPaths_quadraticVariation hF).indicator s).hasRightContinuousPaths)

namespace IsLocalMartingale

/-- Native local square integrability proves the legal existence domain of
the actual angle process, with all positive-lifetime masks retained. -/
theorem hasLocallyIntegrableVariation_quadraticVariation_of_locally_squareIntegrable
    (hM : IsLocalMartingale M F P) (hF : F.IsUsual P)
    (hL : Locally (fun Y ↦ IsSquareIntegrableMartingale Y F P) F M P) :
    HasLocallyIntegrableVariation ((hM.isSemimartingale hF).quadraticVariation hF) F P := by
  let hSM := hM.isSemimartingale hF
  have hQL : Locally (fun Y : ℝ≥0 → Ω → ℝ ↦ ∀ t, Integrable (Y t) P) F
      (hSM.quadraticVariation hF) P := by
    obtain ⟨τ, hτ, hLτ⟩ := hL
    refine ⟨τ, hτ, ?_⟩
    intro n t
    let s : Set Ω := {ω | 0 < τ n ω}
    have hs : MeasurableSet[F 0] s := (hτ.isStoppingTime n).measurableSet_gt 0
    let Y := MeasureTheory.stoppedProcess (fun u ↦ s.indicator (M u)) (τ n)
    have hY : IsSquareIntegrableMartingale Y F P := by
      simpa only [Y, s, bot_eq_zero] using hLτ n
    let hYS : IsSemimartingale Y F P :=
      (hSM.indicator_initial hs).stoppedProcess hF (hτ.isStoppingTime n)
    have he : Indistinguishable (hYS.quadraticVariation hF)
        (MeasureTheory.stoppedProcess
          (fun u ↦ s.indicator (hSM.quadraticVariation hF u)) (τ n)) P :=
      ((hSM.indicator_initial hs).quadraticVariation_stoppedProcess hF
        (hτ.isStoppingTime n)).trans
        ((quadraticVariation_indicator_initial hSM hF hs).stoppedProcess (τ n))
    have hi := (hYS.integrable_quadraticVariation_and_integral_eq hF hY t).1
    simpa only [s, bot_eq_zero] using hi.congr (he.ae_eq t)
  exact HasMonotonePaths.hasLocallyIntegrableVariation_of_locally_integrable
    (hSM.hasMonotonePaths_quadraticVariation hF)
    (hSM.adapted_quadraticVariation hF) hF
    (hSM.hasCadlagPaths_quadraticVariation hF) hQL

/-- The actual selected angle process exists for a native locally-L2 local
martingale and compensates both its raw bracket and its square. The latter
local martingale keeps the possibly nonintegrable original initial square. -/
theorem exists_predictableQuadraticVariation_of_locally_squareIntegrable
    (hM : IsLocalMartingale M F P) (hF : F.IsUsual P)
    (hL : Locally (fun Y ↦ IsSquareIntegrableMartingale Y F P) F M P) :
    ∃ hQ : HasLocallyIntegrableVariation
        ((hM.isSemimartingale hF).quadraticVariation hF) F P,
      let A := (hM.isSemimartingale hF).predictableQuadraticVariation hF hQ
      IsStronglyPredictable F A ∧ (∀ ω, IsCadlagPath (A · ω)) ∧ A 0 = 0 ∧
        HasMonotonePaths A P ∧ HasLocallyIntegrableVariation A F P ∧
        IsLocalMartingale ((hM.isSemimartingale hF).quadraticVariation hF - A) F P ∧
        IsLocalMartingale (fun t ω ↦ (M t ω) ^ 2 - A t ω) F P := by
  have hQ := hM.hasLocallyIntegrableVariation_quadraticVariation_of_locally_squareIntegrable hF hL
  obtain ⟨hp, hc, h0, hm, hv, hR⟩ :=
    (hM.isSemimartingale hF).predictableQuadraticVariation_properties hF hQ
  exact ⟨hQ, hp, hc, h0, hm, hv, hR,
    hM.isLocalMartingale_sq_sub_predictableQuadraticVariation hF hQ⟩

end IsLocalMartingale

end ProbabilityTheory
