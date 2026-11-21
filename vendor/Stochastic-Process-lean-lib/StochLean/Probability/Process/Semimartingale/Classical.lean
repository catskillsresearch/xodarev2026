/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.Semimartingale.LocalMartingale

/-! # Protter III.30: classical semimartingales are semimartingales

The classical source decomposition has an arbitrary local-martingale part and
an adapted finite-variation part. It has exactly the normalization and common
pathwise equality used by `IsDecomposable`, but does not require the local
martingale to be locally square integrable. The arbitrary original initial
random value stays outside both zero-initial components.

The actual fundamental local-martingale decomposition splits the classical
martingale part into a locally square-integrable part and a finite-variation
part. Absorbing the latter into the original finite-variation component proves
equivalence with the existing decomposable predicate. The already proved easy
direction then gives the original good-integrator semimartingale property.

Neither semimartingale behavior nor a square-integrable decomposition is a field
of the classical source predicate. No new component or localization selector,
predictability of the finite-variation part, or initial moment is imposed.
-/

@[expose] public section

open MeasureTheory Filter
open scoped NNReal

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

/-- The classical decomposition uses a general local martingale, with the
same original-initial-value convention as the existing decomposable predicate. -/
def IsClassicalSemimartingale (X : ℝ≥0 → Ω → ℝ) (F : Filtration ℝ≥0 mΩ)
    (P : Measure Ω) : Prop :=
  Adapted F X ∧ HasCadlagPaths X P ∧
    ∃ M A : ℝ≥0 → Ω → ℝ,
      IsLocalMartingale M F P ∧ Adapted F A ∧ HasCadlagPaths A P ∧
      HasFiniteVariationPaths A P ∧ M 0 =ᵐ[P] 0 ∧ A 0 =ᵐ[P] 0 ∧
      Indistinguishable X ((fun _ ↦ X 0) + M + A) P

variable {X : ℝ≥0 → Ω → ℝ} {F : Filtration ℝ≥0 mΩ} {P : Measure Ω}

/-- Forgetting the locally square-integrable field needs no measure-finiteness
or filtration-regularity assumption. -/
theorem IsDecomposable.isClassicalSemimartingale (hX : IsDecomposable X F P) :
    IsClassicalSemimartingale X F P := by
  obtain ⟨ha, hc, M, A, hM, _, haA, hcA, hvA, hM0, hA0, he⟩ := hX
  exact ⟨ha, hc, M, A, hM, haA, hcA, hvA, hM0, hA0, he⟩

variable [IsProbabilityMeasure P]

/-- The actual fundamental decomposition upgrades the classical source
decomposition to the existing locally square-integrable decomposition. -/
theorem IsClassicalSemimartingale.isDecomposable (hX : IsClassicalSemimartingale X F P)
    (hF : F.IsUsual P) : IsDecomposable X F P := by
  obtain ⟨ha, hc, M, A, hM, haA, hcA, hvA, hM0, hA0, he⟩ := hX
  obtain ⟨N, D, hN, hD, hD0, hN0, hvD, hsplit, _, hN2⟩ :=
    hM.exists_fundamental_decomposition_of_pos hF (β := 1) zero_lt_one
  have hv : HasFiniteVariationPaths (D + A) P := by
    filter_upwards [hvD.hasFiniteVariationPaths, hvA] with ω hd ha
    exact StochLean.locallyBoundedVariationOn_add hd ha
  have hn0 : N 0 =ᵐ[P] 0 := by
    rw [hN0]
    exact hM0
  have ha0 : (D + A) 0 =ᵐ[P] 0 := by
    filter_upwards [hA0] with ω hω
    change D 0 ω + A 0 ω = 0
    rw [congrFun hD0 ω, Pi.zero_apply, zero_add]
    exact hω
  have heParts : (fun _ ↦ X 0) + M + A = (fun _ ↦ X 0) + N + (D + A) := by
    rw [hsplit]
    simp only [add_assoc]
  exact ⟨ha, hc, N, D + A, hN, hN2, hD.1.add haA, hD.2.1.add hcA,
    hv, hn0, ha0, heParts ▸ he⟩

/-- The source classical and decomposable predicates agree by actual
fundamental decomposition, not by changing either definition. -/
theorem isClassicalSemimartingale_iff_isDecomposable (hF : F.IsUsual P) :
    IsClassicalSemimartingale X F P ↔ IsDecomposable X F P :=
  ⟨fun h ↦ h.isDecomposable hF, IsDecomposable.isClassicalSemimartingale⟩

/-- Protter III.30 in the original elementary-good-integrator sense:
every classical semimartingale is a semimartingale. -/
theorem IsClassicalSemimartingale.isSemimartingale (hX : IsClassicalSemimartingale X F P)
    (hF : F.IsUsual P) : IsSemimartingale X F P :=
  (hX.isDecomposable hF).isSemimartingale hF

/-- General local martingales, including nonintegrable initial values,
belong to the classical source domain by the actual normalized decomposition. -/
theorem IsLocalMartingale.isClassicalSemimartingale (hX : IsLocalMartingale X F P)
    (hF : F.IsUsual P) : IsClassicalSemimartingale X F P :=
  (hX.isDecomposable hF).isClassicalSemimartingale

end ProbabilityTheory
