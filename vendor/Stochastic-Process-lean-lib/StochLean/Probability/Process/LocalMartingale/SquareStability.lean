/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Martingale.OptionalSampling.ContinuousLp
public import StochLean.Probability.Process.Measurability.InitialMask

/-! # Initial masking and stability of finite-time L2 martingales

The stable local property includes common-event cadlag paths. No global second
moment bound is introduced.
-/

@[expose] public section

open MeasureTheory Set
open scoped NNReal ENNReal

namespace MeasureTheory.Martingale

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {F : Filtration ℝ≥0 mΩ}
  {P : Measure Ω} {X : ℝ≥0 → Ω → ℝ}

theorem indicator_initial (hX : Martingale X F P)
    {s : Set Ω} (hs : MeasurableSet[F 0] s) :
    Martingale (fun t ↦ s.indicator (X t)) F P := by
  refine ⟨fun t ↦ (hX.stronglyAdapted t).indicator (F.mono bot_le s hs), ?_⟩
  intro u t hut
  refine (condExp_indicator (hX.integrable t) (F.mono bot_le s hs)).trans ?_
  filter_upwards [hX.condExp_ae_eq hut] with ω hω
  by_cases h : ω ∈ s <;> simp [h, hω]

end MeasureTheory.Martingale

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {F : Filtration ℝ≥0 mΩ}
  {P : Measure Ω} {X Y : ℝ≥0 → Ω → ℝ}

theorem IsSquareIntegrableMartingale.indicator_initial
    (hX : IsSquareIntegrableMartingale X F P) {s : Set Ω} (hs : MeasurableSet[F 0] s) :
    IsSquareIntegrableMartingale (fun t ↦ s.indicator (X t)) F P :=
  ⟨hX.1.indicator_initial hs, fun t ↦ (hX.2 t).indicator (F.le 0 s hs)⟩

theorem IsSquareIntegrableMartingale.congr
    (hX : IsSquareIntegrableMartingale X F P) (ha : Adapted F Y)
    (heq : Indistinguishable X Y P) : IsSquareIntegrableMartingale Y F P :=
  ⟨hX.1.congr ha.stronglyAdapted heq.ae_eq, fun t ↦ (hX.2 t).ae_eq (heq.ae_eq t)⟩

theorem isStable_cadlagSquareIntegrableMartingale [IsFiniteMeasure P]
    [SigmaFiniteFiltration P F] (hF : F.IsUsual P) :
    IsStable F (fun Y ↦ IsSquareIntegrableMartingale Y F P ∧ HasCadlagPaths Y P) := by
  intro Y hY τ hτ
  have hs : MeasurableSet[F 0] {ω | 0 < τ ω} := hτ.measurableSet_gt 0
  have hc := hY.2.indicator {ω | 0 < τ ω}
  exact ⟨(hY.1.indicator_initial hs).stoppedProcess_of_usual hF
    hc.hasRightContinuousPaths hτ, hc.stoppedProcess τ⟩

end ProbabilityTheory
