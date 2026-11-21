/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.FiniteVariation.CompensatorIntegrable
public import StochLean.Probability.Martingale.Doob.PredictableClassD
public import StochLean.Probability.Martingale.MonotonePaths
public import StochLean.Probability.Process.LocalMartingale.Reducing

/-! # Increasing processes have increasing predictable compensators

An adapted increasing integrable-variation process with integrable initial
value is a Class D submartingale. Applied to its negative, the actual general
Class D Doob theorem constructs an increasing predictable compensator.
Negating the resulting true UI martingale gives the compensator convention
`X - B`. Existing predictable FV uniqueness then identifies any supplied
normalized predictable IV compensator with this genuinely constructed B.

The auxiliary comparison does not assume the supplied candidate exists for
every source. The separate existence theorem invokes the already proved
actual integrable-variation compensator construction. The original initial
value remains arbitrary and is retained in the expectation identity.
No Yoeurp lemma or semimartingale assumption is used.
-/

@[expose] public section

open MeasureTheory Filter
open scoped NNReal

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
  {F : Filtration ℝ≥0 mΩ} {X A : ℝ≥0 → Ω → ℝ}

/-- Any actual normalized predictable IV compensator of an increasing IV
source is increasing. The candidate starts at zero only almost surely and
its remainder is only required to be a local martingale. -/
theorem HasIntegrableVariation.hasMonotonePaths_predictable_compensator
    (hvX : HasIntegrableVariation X P) (haX : Adapted F X) (hF : F.IsUsual P)
    (hcX : HasCadlagPaths X P) (hi0 : Integrable (X 0) P) (hmX : HasMonotonePaths X P)
    (hpA : IsStronglyPredictable F A) (hvA : HasIntegrableVariation A P)
    (hA0 : A 0 =ᵐ[P] 0) (hM : IsLocalMartingale (X - A) F P) :
    HasMonotonePaths A P := by
  have hXD : IsClassD X F P := hvX.isClassD haX hF hcX hi0
  have hNegX : Supermartingale (-X) F P := (hmX.submartingale haX hXD.integrable).neg
  have hcNegX : HasCadlagPaths (-X) P := hcX.continuous_comp continuous_neg
  obtain ⟨B, _, hpB, hcB, hB0, hmB, hvB, _, huB, _, _, _, _, _⟩ :=
    hNegX.exists_predictable_doob_of_classD hXD.neg hF hcNegX
  have heNeg : -(-X + B) = X - B := by
    funext t ω
    change -(-X t ω + B t ω) = X t ω - B t ω
    ring
  have hu : IsUIMartingale (X - B) F P := heNeg ▸ huB.neg
  have hMB : IsLocalMartingale (X - B) F P :=
    hu.1.isLocalMartingale (hcX.sub hcB)
  have h0 : A 0 =ᵐ[P] B 0 := by
    filter_upwards [hA0] with ω hω
    exact hω.trans (congrFun hB0 ω).symm
  have he : Indistinguishable ((X - A) + A) ((X - B) + B) P := by
    filter_upwards with ω t
    simp only [Pi.add_apply, Pi.sub_apply, sub_add_cancel]
  have hAB := (indistinguishable_parts_of_predictable_finiteVariation_decomposition
    hF hM hMB hpA hpB hvA.hasFiniteVariationPaths hvB.hasFiniteVariationPaths h0 he).1
  exact HasMonotonePaths.congr hAB.symm hmB

/-- Actual existence and uniqueness of an increasing predictable IV
compensator. The true UI remainder and the exact mean identity retain the
original, possibly nonzero initial random value. -/
theorem HasIntegrableVariation.exists_unique_monotone_predictable_compensator
    (hvX : HasIntegrableVariation X P) (haX : Adapted F X) (hF : F.IsUsual P)
    (hcX : HasCadlagPaths X P) (hi0 : Integrable (X 0) P) (hmX : HasMonotonePaths X P) :
    ∃ A : ℝ≥0 → Ω → ℝ,
      IsStronglyPredictable F A ∧ (∀ ω, IsCadlagPath (A · ω)) ∧ A 0 = 0 ∧
      HasMonotonePaths A P ∧ HasIntegrableVariation A P ∧ IsUIMartingale (X - A) F P ∧
      (∀ t, Integrable (A t) P ∧
        (∫ ω, A t ω ∂P) = (∫ ω, X t ω ∂P) - ∫ ω, X 0 ω ∂P) ∧
      ∀ B : ℝ≥0 → Ω → ℝ,
        IsStronglyPredictable F B → HasFiniteVariationPaths B P →
        B 0 =ᵐ[P] 0 → IsLocalMartingale (X - B) F P → Indistinguishable A B P := by
  obtain ⟨A, hpA, hcA, hA0, hvA, huA, hmean, huniq⟩ :=
    hvX.exists_unique_predictable_compensator haX hF hcX hi0
  have hmA : HasMonotonePaths A P :=
    hvX.hasMonotonePaths_predictable_compensator haX hF hcX hi0 hmX hpA hvA
      (Eventually.of_forall fun ω ↦ congrFun hA0 ω)
      (huA.1.isLocalMartingale (hcX.sub (Eventually.of_forall hcA)))
  exact ⟨A, hpA, hcA, hA0, hmA, hvA, huA, hmean, huniq⟩

end ProbabilityTheory
