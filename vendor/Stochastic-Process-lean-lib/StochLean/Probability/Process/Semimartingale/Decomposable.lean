/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.Semimartingale.LocalL2Martingale
public import StochLean.Probability.Process.Semimartingale.FiniteVariation
public import StochLean.Probability.Process.Semimartingale.Stability

/-! # Protter II.9: the decomposable easy direction

Decomposable is a source decomposition predicate, not a definition of semimartingale.
The martingale component is locally square integrable, while the FV component need
not be predictable. Equality of processes is indistinguishability; no canonical
decomposition or general local-martingale decomposition theorem is asserted here.
-/

@[expose] public section

open MeasureTheory
open scoped NNReal ENNReal

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

def IsDecomposable (X : ℝ≥0 → Ω → ℝ) (F : Filtration ℝ≥0 mΩ) (P : Measure Ω) : Prop :=
  Adapted F X ∧ HasCadlagPaths X P ∧
    ∃ M A : ℝ≥0 → Ω → ℝ,
      IsLocalMartingale M F P ∧ Locally (fun Y ↦ IsSquareIntegrableMartingale Y F P) F M P ∧
      Adapted F A ∧ HasCadlagPaths A P ∧ HasFiniteVariationPaths A P ∧
      M 0 =ᵐ[P] 0 ∧ A 0 =ᵐ[P] 0 ∧
      Indistinguishable X ((fun _ ↦ X 0) + M + A) P

variable {X : ℝ≥0 → Ω → ℝ} {F : Filtration ℝ≥0 mΩ} {P : Measure Ω}
  [IsFiniteMeasure P] [SigmaFiniteFiltration P F]

theorem IsDecomposable.isSemimartingale (hX : IsDecomposable X F P) (hF : F.IsUsual P) :
    IsSemimartingale X F P := by
  obtain ⟨ha, _, M, A, hM, hMl2, hAa, hAc, hAv, _, _, heq⟩ := hX
  have hMs := isSemimartingale_of_locally_squareIntegrableMartingale hF hM.2.1 hMl2
  have hAs := hAv.isSemimartingale hAa hF hAc
  exact ((isSemimartingale_const_initial (ha 0)).add hMs |>.add hAs).congr_of_adapted heq.symm ha

end ProbabilityTheory
