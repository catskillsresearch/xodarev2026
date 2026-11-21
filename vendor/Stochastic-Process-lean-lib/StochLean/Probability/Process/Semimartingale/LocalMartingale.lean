/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.LocalMartingale.FundamentalDecomposition
public import StochLean.Probability.Process.Semimartingale.Decomposable

/-! # General local martingales are source semimartingales

The actual fundamental local-martingale decomposition supplies a locally
square-integrable part and a finite-variation part. Applying it after centering
the original initial random value gives the existing normalized decomposable
predicate. Its already proved elementary-integrator easy direction yields the
source semimartingale predicate, not a new definition by decomposition.

No integrability of the original initial value, continuity, bounded jumps,
square-integrability certificate or semimartingale premise is assumed.
-/

@[expose] public section

open MeasureTheory Filter
open scoped NNReal

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
  {F : Filtration ℝ≥0 mΩ} {X : ℝ≥0 → Ω → ℝ}

/-- Actual fundamental decomposition gives the normalized source decomposable
predicate. The unmasked initial random value remains outside both zero-initial
parts and need not have a first or second moment. -/
theorem IsLocalMartingale.isDecomposable (hX : IsLocalMartingale X F P)
    (hF : F.IsUsual P) : IsDecomposable X F P := by
  let I : ℝ≥0 → Ω → ℝ := fun _ ↦ X 0
  let Y := X - I
  have hI : IsLocalMartingale I F P :=
    (isContinuousLocalMartingale_const_initial (hX.1 0)).1
  have hY : IsLocalMartingale Y F P := hX.sub hI hF
  have hY0 : Y 0 = 0 := by
    funext ω
    exact sub_self (X 0 ω)
  obtain ⟨N, D, hN, hD, hD0, hN0, hvD, he, _, hN2⟩ :=
    hY.exists_fundamental_decomposition_of_pos hF (β := 1) zero_lt_one
  refine ⟨hX.1, hX.2.1, N, D, hN, hN2, hD.1, hD.2.1,
    hvD.hasFiniteVariationPaths,
    Eventually.of_forall (fun ω ↦ congrFun (hN0.trans hY0) ω),
    Eventually.of_forall (fun ω ↦ congrFun hD0 ω), ?_⟩
  filter_upwards with ω t
  have h := congrFun (congrFun he t) ω
  change X t ω - X 0 ω = N t ω + D t ω at h
  change X t ω = (X 0 ω + N t ω) + D t ω
  linarith only [h]

/-- The corollary to Protter III.30: every actual cadlag local martingale is a semimartingale
in the original good-integrator sense, through the proved easy direction. -/
theorem IsLocalMartingale.isSemimartingale (hX : IsLocalMartingale X F P)
    (hF : F.IsUsual P) : IsSemimartingale X F P :=
  (hX.isDecomposable hF).isSemimartingale hF

end ProbabilityTheory

namespace MeasureTheory.Martingale

open ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
  {F : Filtration ℝ≥0 mΩ} {X : ℝ≥0 → Ω → ℝ}

/-- In particular, a true cadlag martingale needs no square-integrability
or global uniform-integrability assumption to be a source semimartingale. -/
theorem isSemimartingale_of_cadlag (hX : Martingale X F P)
    (hF : F.IsUsual P) (hc : HasCadlagPaths X P) : IsSemimartingale X F P :=
  (hX.isLocalMartingale hc).isSemimartingale hF

end MeasureTheory.Martingale
