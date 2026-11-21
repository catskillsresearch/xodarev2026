/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Martingale.Doob.PredictableLocal

/-! # The normalized source form of the local Doob--Meyer theorem

The actual general local construction retains the original random initial
value. Subtracting its constant martingale gives the book's normalized form
X = X(0) + M - A, with both M and A starting exactly at zero. Uniqueness uses
the existing predictable finite-variation local-martingale theorem and only
requires finite variation of a competing predictable part, not local
integrability of its variation.
-/

@[expose] public section

open ProbabilityTheory Filter
open scoped NNReal

namespace MeasureTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
  {F : Filtration ℝ≥0 mΩ} {X : ℝ≥0 → Ω → ℝ}

/-- Protter III.16 in the exact normalized source form, with uniqueness up
to indistinguishability. No integrability assumption on a proposed competing
finite-variation part is needed. The original process is any cadlag
supermartingale, not necessarily Class D. -/
theorem Supermartingale.exists_unique_predictable_doob_local_decomposition
    (hX : Supermartingale X F P) (hF : F.IsUsual P) (hc : HasCadlagPaths X P) :
    ∃ M A : ℝ≥0 → Ω → ℝ,
      IsLocalMartingale M F P ∧ M 0 = 0 ∧
      IsStronglyPredictable F A ∧ (∀ ω, IsCadlagPath (A · ω)) ∧ A 0 = 0 ∧
      HasMonotonePaths A P ∧ HasLocallyIntegrableVariation A F P ∧
      X = (fun _ ↦ X 0) + M - A ∧
      (∀ t, Integrable (A t) P ∧
        (∫ ω, A t ω ∂P) ≤ (∫ ω, X 0 ω ∂P) - ∫ ω, X t ω ∂P) ∧
      ∀ N B : ℝ≥0 → Ω → ℝ, IsLocalMartingale N F P →
        IsStronglyPredictable F B → HasFiniteVariationPaths B P → B 0 =ᵐ[P] 0 →
        Indistinguishable X ((fun _ ↦ X 0) + N - B) P →
        Indistinguishable M N P ∧ Indistinguishable A B P := by
  obtain ⟨A, hpA, hcA, hA0, hmA, hvA, hL, hiA⟩ :=
    hX.exists_predictable_doob_local_decomposition hF hc
  let I : ℝ≥0 → Ω → ℝ := fun _ ↦ X 0
  have hI : Martingale I F P :=
    martingale_const_fun F P (hX.stronglyAdapted 0) (hX.integrable 0)
  have hcI : HasCadlagPaths I P := Eventually.of_forall fun ω ↦
    IsContinuousPath.isCadlagPath (continuous_const : Continuous (fun _ : ℝ≥0 ↦ X 0 ω))
  have hIL : IsLocalMartingale I F P := hI.isLocalMartingale hcI
  let M := X + A - I
  have hM : IsLocalMartingale M F P := hL.sub hIL hF
  have hM0 : M 0 = 0 := by
    funext ω
    change X 0 ω + A 0 ω - X 0 ω = 0
    rw [congrFun hA0 ω]
    simp only [Pi.zero_apply, add_zero, sub_self]
  have he : X = I + M - A := by
    funext t ω
    change X t ω = X 0 ω + (X t ω + A t ω - X 0 ω) - A t ω
    ring
  refine ⟨M, A, hM, hM0, hpA, hcA, hA0, hmA, hvA, he, hiA, ?_⟩
  intro N B hN hpB hvB hB0 heB
  have hNB : IsLocalMartingale (N + I) F P := hN.add hIL hF
  have haXB : Adapted F (X + B) := hX.stronglyAdapted.adapted.add hpB.stronglyAdapted.adapted
  have heNB : Indistinguishable (N + I) (X + B) P := by
    filter_upwards [heB] with ω hω t
    have h := hω t
    change X t ω = X 0 ω + N t ω - B t ω at h
    change N t ω + X 0 ω = X t ω + B t ω
    linarith only [h]
  have hXB : IsLocalMartingale (X + B) F P := hNB.congr hF haXB heNB
  have hA00 : A 0 =ᵐ[P] 0 := Eventually.of_forall fun ω ↦ congrFun hA0 ω
  have hAB : Indistinguishable A B P :=
    indistinguishable_of_predictable_finiteVariation_localMartingale_add hF hL hXB
      hpA hpB hvA.hasFiniteVariationPaths hvB
      (hA00.trans hB0.symm)
  refine ⟨?_, hAB⟩
  filter_upwards [heB, hAB] with ω hω hABω t
  have h := hω t
  change X t ω = X 0 ω + N t ω - B t ω at h
  change X t ω + A t ω - X 0 ω = N t ω
  rw [hABω t]
  linarith only [h]

end MeasureTheory
