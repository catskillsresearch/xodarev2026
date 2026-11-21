/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.Semimartingale.LocalMartingale
public import StochLean.Probability.Process.Semimartingale.Subtraction
public import StochLean.Probability.Process.Semimartingale.Quasimartingale.RaoLocal
public import StochLean.Probability.Martingale.Doob.PredictableLocal

/-! # Quasimartingales and one-sided martingales are semimartingales

Actual Rao and local Doob--Meyer existence provide the local-martingale and
finite-variation parts. The general local-martingale bridge and the original
good-integrator algebra give Protter III.31--III.32 and its submartingale
corollary. No Class D, global UI, boundedness or proposed decomposition is
required for the one-sided results.
-/

@[expose] public section

open MeasureTheory Filter
open scoped NNReal

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
  {F : Filtration ℝ≥0 mΩ} {X : ℝ≥0 → Ω → ℝ}

/-- Protter III.31, through actual Rao existence and the source good-integrator
predicate. Cadlag regularity is part of the existing quasimartingale owner. -/
theorem IsQuasimartingale.isSemimartingale (hX : IsQuasimartingale X F P)
    (hF : F.IsUsual P) : IsSemimartingale X F P := by
  obtain ⟨M, A, hM, hpA, hcA, _, hvA, _, he, _⟩ :=
    hX.exists_unique_rao_decomposition hF
  rw [he]
  exact (hM.isSemimartingale hF).add
    (hvA.hasFiniteVariationPaths.isSemimartingale hpA.stronglyAdapted.adapted hF
      (Eventually.of_forall hcA))

end ProbabilityTheory

namespace MeasureTheory

open ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
  {F : Filtration ℝ≥0 mΩ} {X : ℝ≥0 → Ω → ℝ}

/-- Protter III.32: an arbitrary cadlag supermartingale is a source
semimartingale; actual local Doob--Meyer supplies the decomposition. -/
theorem Supermartingale.isSemimartingale (hX : Supermartingale X F P)
    (hF : F.IsUsual P) (hc : HasCadlagPaths X P) : IsSemimartingale X F P := by
  obtain ⟨A, hpA, hcA, _, _, hvA, hM, _⟩ :=
    hX.exists_predictable_doob_local_decomposition hF hc
  have hs := (hM.isSemimartingale hF).sub
    (hvA.hasFiniteVariationPaths.isSemimartingale hpA.stronglyAdapted.adapted hF
      (Eventually.of_forall hcA))
  simpa only [add_sub_cancel_right] using hs

/-- The submartingale corollary retains almost-sure cadlag paths and does
not add any Class D or uniform-integrability requirement. -/
theorem Submartingale.isSemimartingale (hX : Submartingale X F P)
    (hF : F.IsUsual P) (hc : HasCadlagPaths X P) : IsSemimartingale X F P := by
  have hs := (hX.neg.isSemimartingale hF (hc.continuous_comp continuous_neg)).neg
  simpa only [neg_neg] using hs

end MeasureTheory
