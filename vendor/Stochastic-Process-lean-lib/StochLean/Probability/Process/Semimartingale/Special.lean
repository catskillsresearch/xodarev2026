/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.Semimartingale.Classical
public import StochLean.Probability.Process.Semimartingale.Quasimartingale.RaoLocal
public import StochLean.Probability.Martingale.Doob.PredictableLocalCanonical

/-! # Special semimartingales and uniqueness of their source decomposition

The special source predicate is the classical decomposition with a predictable
finite-variation part. Both components start at zero almost surely, and the
original random initial value remains outside the decomposition. The original
good-integrator semimartingale property is a conclusion, not an assumed field.

Protter III.34 follows from the proved uniqueness of predictable FV
local-martingale decompositions. Competing parts need only have the stated
finite-variation and initial-value properties, with no variation moment or
extra path-regularity assumption.

The actual Rao construction gives special decompositions of quasimartingales;
the actual local Doob construction gives them for cadlag supermartingales.
These consumers do not assume Class D, a proposed decomposition, or an extra
initial moment. No canonical component selector is introduced here.
-/

@[expose] public section

open MeasureTheory Filter
open scoped NNReal

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

/-- A classical source decomposition whose normalized finite-variation part
is predictable. The semimartingale property is derived separately. -/
def IsSpecialSemimartingale (X : ℝ≥0 → Ω → ℝ) (F : Filtration ℝ≥0 mΩ)
    (P : Measure Ω) : Prop :=
  Adapted F X ∧ HasCadlagPaths X P ∧
    ∃ M A : ℝ≥0 → Ω → ℝ,
      IsLocalMartingale M F P ∧ IsStronglyPredictable F A ∧ HasCadlagPaths A P ∧
      HasFiniteVariationPaths A P ∧ M 0 =ᵐ[P] 0 ∧ A 0 =ᵐ[P] 0 ∧
      Indistinguishable X ((fun _ ↦ X 0) + M + A) P

variable {X : ℝ≥0 → Ω → ℝ} {F : Filtration ℝ≥0 mΩ} {P : Measure Ω}

/-- Forgetting predictability uses its actual adaptedness implication and
requires neither a finite measure nor a usual filtration. -/
theorem IsSpecialSemimartingale.isClassicalSemimartingale
    (hX : IsSpecialSemimartingale X F P) : IsClassicalSemimartingale X F P := by
  obtain ⟨ha, hc, M, A, hM, hpA, hcA, hvA, hM0, hA0, he⟩ := hX
  exact ⟨ha, hc, M, A, hM, hpA.stronglyAdapted.adapted, hcA, hvA, hM0, hA0, he⟩

variable [IsProbabilityMeasure P]

/-- Special semimartingales satisfy the original good-integrator predicate
through the actual classical-semimartingale theorem. -/
theorem IsSpecialSemimartingale.isSemimartingale (hX : IsSpecialSemimartingale X F P)
    (hF : F.IsUsual P) : IsSemimartingale X F P :=
  hX.isClassicalSemimartingale.isSemimartingale hF

/-- Protter III.34: both normalized parts are unique up to indistinguishability.
The competing finite-variation part is normalized only almost surely; neither
its variation integrability nor a separate cadlag hypothesis is needed. -/
theorem IsSpecialSemimartingale.exists_unique_decomposition
    (hX : IsSpecialSemimartingale X F P) (hF : F.IsUsual P) :
    ∃ M A : ℝ≥0 → Ω → ℝ,
      IsLocalMartingale M F P ∧ IsStronglyPredictable F A ∧ HasCadlagPaths A P ∧
      HasFiniteVariationPaths A P ∧ M 0 =ᵐ[P] 0 ∧ A 0 =ᵐ[P] 0 ∧
      Indistinguishable X ((fun _ ↦ X 0) + M + A) P ∧
      ∀ N B : ℝ≥0 → Ω → ℝ,
        IsLocalMartingale N F P → IsStronglyPredictable F B →
        HasFiniteVariationPaths B P → B 0 =ᵐ[P] 0 →
        Indistinguishable X ((fun _ ↦ X 0) + N + B) P →
        Indistinguishable M N P ∧ Indistinguishable A B P := by
  obtain ⟨_, _, M, A, hM, hpA, hcA, hvA, hM0, hA0, he⟩ := hX
  refine ⟨M, A, hM, hpA, hcA, hvA, hM0, hA0, he, ?_⟩
  intro N B hN hpB hvB hB0 heB
  have heParts : Indistinguishable (M + A) (N + B) P := by
    filter_upwards [he, heB] with ω hω hBω t
    have ht := (hω t).symm.trans (hBω t)
    change (X 0 ω + M t ω) + A t ω = (X 0 ω + N t ω) + B t ω at ht
    have hsum : X 0 ω + (M t ω + A t ω) = X 0 ω + (N t ω + B t ω) := by
      simpa only [add_assoc] using ht
    exact add_left_cancel hsum
  have hu := indistinguishable_parts_of_predictable_finiteVariation_decomposition
    hF hM hN hpA hpB hvA hvB (hA0.trans hB0.symm) heParts
  exact ⟨hu.2, hu.1⟩

/-- The actual Rao decomposition yields a special semimartingale, after
centering its local-martingale component by the original initial random value. -/
theorem IsQuasimartingale.isSpecialSemimartingale (hX : IsQuasimartingale X F P)
    (hF : F.IsUsual P) : IsSpecialSemimartingale X F P := by
  obtain ⟨M, A, hM, hpA, hcA, hA0, hvA, _, he, _⟩ :=
    hX.exists_unique_rao_decomposition hF
  let I : ℝ≥0 → Ω → ℝ := fun _ ↦ X 0
  let N := M - I
  have hI : IsLocalMartingale I F P :=
    (isContinuousLocalMartingale_const_initial (hX.adapted 0)).1
  have hN : IsLocalMartingale N F P := hM.sub hI hF
  have hM0 : M 0 = X 0 := by
    have h := congrArg (fun Y : ℝ≥0 → Ω → ℝ ↦ Y 0) he
    change X 0 = M 0 + A 0 at h
    rw [hA0, add_zero] at h
    exact h.symm
  have hN0 : N 0 = 0 := by
    change M 0 - X 0 = 0
    rw [hM0, sub_self]
  refine ⟨hX.adapted, hX.hasCadlagPaths, N, A, hN, hpA,
    Eventually.of_forall hcA, hvA.hasFiniteVariationPaths,
    Eventually.of_forall (fun ω ↦ congrFun hN0 ω),
    Eventually.of_forall (fun ω ↦ congrFun hA0 ω), ?_⟩
  filter_upwards with ω t
  have ht := congrFun (congrFun he t) ω
  change X t ω = M t ω + A t ω at ht
  change X t ω = (X 0 ω + (M t ω - X 0 ω)) + A t ω
  linarith only [ht]

end ProbabilityTheory

namespace MeasureTheory.Supermartingale

open ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
  {F : Filtration ℝ≥0 mΩ} {X : ℝ≥0 → Ω → ℝ}

/-- The actual local Doob decomposition makes every cadlag supermartingale
special. Its predictable finite-variation part is the negative compensator. -/
theorem isSpecialSemimartingale (hX : Supermartingale X F P)
    (hF : F.IsUsual P) (hc : HasCadlagPaths X P) : IsSpecialSemimartingale X F P := by
  obtain ⟨M, A, hM, hM0, hpA, hcA, hA0, _, hvA, he, _, _⟩ :=
    hX.exists_unique_predictable_doob_local_decomposition hF hc
  have hp : IsStronglyPredictable F (-A) := hpA.neg
  have hcNeg : HasCadlagPaths (-A) P :=
    HasCadlagPaths.continuous_comp (X := A) (Eventually.of_forall hcA) continuous_neg
  have hNeg0 : (-A) 0 = 0 := by
    change -A 0 = 0
    rw [hA0, neg_zero]
  refine ⟨hX.stronglyAdapted.adapted, hc, M, -A, hM, hp, hcNeg,
    hvA.neg.hasFiniteVariationPaths,
    Eventually.of_forall (fun ω ↦ congrFun hM0 ω),
    Eventually.of_forall (fun ω ↦ congrFun hNeg0 ω), ?_⟩
  have he' : X = (fun _ ↦ X 0) + M + -A := by
    simpa only [sub_eq_add_neg] using he
  exact Eventually.of_forall fun ω t ↦ congrFun (congrFun he' t) ω

end MeasureTheory.Supermartingale
