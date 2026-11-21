/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.Semimartingale.L2Martingale
public import StochLean.Probability.Process.Semimartingale.Localization
public import StochLean.Probability.Process.LocalMartingale.ContinuousSquareLocalization

/-! # Locally square-integrable and continuous local martingale examples

The existing bounded masked localization supplies the L2 witnesses for continuous local
martingales. No L1 or L2 assumption on their unmasked initial values is introduced.
-/

@[expose] public section

open MeasureTheory
open scoped NNReal ENNReal

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {F : Filtration ℝ≥0 mΩ}
  {P : Measure Ω} [IsFiniteMeasure P] [SigmaFiniteFiltration P F]
  {X : ℝ≥0 → Ω → ℝ}

theorem isSemimartingale_of_locally_squareIntegrableMartingale
    (hF : F.IsUsual P) (hc : HasCadlagPaths X P)
    (hL : Locally (fun Y ↦ IsSquareIntegrableMartingale Y F P) F X P) :
    IsSemimartingale X F P := by
  obtain ⟨τ, hτ, hY⟩ := hL
  apply isSemimartingale_of_preLocalizingSequence
    (hτ.toIsPreLocalizingSequence.adapted_of_masked hF
      (fun n ↦ (hY n).1.stronglyAdapted.adapted)) hc hτ.toIsPreLocalizingSequence
  intro n
  exact (hY n).1.isSemimartingale_of_memLp hF
    ((hc.indicator {ω | 0 < τ n ω}).stoppedProcess (τ n)) (hY n).2

theorem IsContinuousLocalMartingale.isSemimartingale
    (hX : IsContinuousLocalMartingale X F P) (hF : F.IsUsual P) :
    IsSemimartingale X F P :=
  isSemimartingale_of_locally_squareIntegrableMartingale hF hX.1.2.1
    (hX.locally_squareIntegrableMartingale hF)

end ProbabilityTheory
