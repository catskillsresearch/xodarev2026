/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.Semimartingale.Quasimartingale.Rao
public import StochLean.Probability.Martingale.Doob.PredictableLocalTerminal
public import StochLean.Probability.Martingale.Doob.PredictableUniqueness
public import StochLean.Probability.Process.FiniteVariation.IntegrableAlgebra

/-! # Rao's local-martingale and predictable-variation decomposition

Protter III.18 is obtained from the actual positive-supermartingale
decomposition of III.17 and the actual local Doob construction of III.16.
The positive coordinates have mean bounded below by zero. Their genuinely
constructed increasing compensators therefore have integrable full-half-line
variation, not only local integrable variation.

Subtracting the two local martingales and reversing the order of the two
compensators gives an exact identity for the original quasimartingale. The
predictable variation part starts exactly at zero, so the original initial
random value remains in the local martingale. The existing predictable FV
uniqueness theorem identifies both parts against any other normalized
predictable FV local-martingale decomposition.

No candidate decomposition, terminal, convergence certificate, or new
process selector is assumed or defined.
-/

@[expose] public section

open MeasureTheory Filter
open scoped NNReal

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
  {F : Filtration ℝ≥0 mΩ} {X : ℝ≥0 → Ω → ℝ}

/-- Rao's theorem, Protter III.18: actual existence and uniqueness of the
normalized predictable variation and local-martingale parts. Whole-half-line
integrable variation is obtained here, strengthening local integrability.
Uniqueness only requires finite variation of the competing predictable part. -/
theorem IsQuasimartingale.exists_unique_rao_decomposition
    (hX : IsQuasimartingale X F P) (hF : F.IsUsual P) :
    ∃ M A : ℝ≥0 → Ω → ℝ,
      IsLocalMartingale M F P ∧ IsStronglyPredictable F A ∧
      (∀ ω, IsCadlagPath (A · ω)) ∧ A 0 = 0 ∧ HasIntegrableVariation A P ∧
      HasLocallyIntegrableVariation A F P ∧ X = M + A ∧
      ∀ N B : ℝ≥0 → Ω → ℝ,
        IsLocalMartingale N F P → IsStronglyPredictable F B →
        HasFiniteVariationPaths B P → B 0 =ᵐ[P] 0 →
        Indistinguishable X (N + B) P →
        Indistinguishable M N P ∧ Indistinguishable A B P := by
  obtain ⟨Y, Z, hY, hZ, hcY, hcZ, hn, heX, _, _⟩ :=
    hX.exists_nonnegative_cadlag_supermartingale_decomposition hF
  have hbY (t : ℝ≥0) : 0 ≤ ∫ ω, Y t ω ∂P :=
    integral_nonneg_of_ae (hn.mono fun _ hω ↦ (hω t).1)
  have hbZ (t : ℝ≥0) : 0 ≤ ∫ ω, Z t ω ∂P :=
    integral_nonneg_of_ae (hn.mono fun _ hω ↦ (hω t).2)
  obtain ⟨AY, _, hpAY, hcAY, hAY0, _, _, hvAY, hMY, _⟩ :=
    hY.exists_predictable_doob_integrable_terminal_of_integral_bounded_below hF hcY hbY
  obtain ⟨AZ, _, hpAZ, hcAZ, hAZ0, _, _, hvAZ, hMZ, _⟩ :=
    hZ.exists_predictable_doob_integrable_terminal_of_integral_bounded_below hF hcZ hbZ
  let M := (Y + AY) - (Z + AZ)
  let A := AZ - AY
  have hM : IsLocalMartingale M F P := hMY.sub hMZ hF
  have hpA : IsStronglyPredictable F A := hpAZ.sub hpAY
  have hcA (ω : Ω) : IsCadlagPath (A · ω) := (hcAZ ω).sub (hcAY ω)
  have hA0 : A 0 = 0 := by
    change AZ 0 - AY 0 = 0
    rw [hAZ0, hAY0, sub_self]
  have hvA : HasIntegrableVariation A P :=
    hvAZ.sub hvAY hpAZ.stronglyAdapted.adapted hpAY.stronglyAdapted.adapted hF
      (Eventually.of_forall hcAZ) (Eventually.of_forall hcAY)
  have he : X = M + A := by
    rw [heX]
    funext t ω
    change Y t ω - Z t ω =
      ((Y t ω + AY t ω) - (Z t ω + AZ t ω)) + (AZ t ω - AY t ω)
    ring
  refine ⟨M, A, hM, hpA, hcA, hA0, hvA, hvA.hasLocallyIntegrableVariation, he, ?_⟩
  intro N B hN hpB hvB hB0 heB
  have h0 : A 0 =ᵐ[P] B 0 := by
    filter_upwards [hB0] with ω hω
    rw [hA0]
    exact hω.symm
  have hparts := indistinguishable_parts_of_predictable_finiteVariation_decomposition
    hF hM hN hpA hpB hvA.hasFiniteVariationPaths hvB h0
    (show Indistinguishable (M + A) (N + B) P from he ▸ heB)
  exact ⟨hparts.2, hparts.1⟩

end ProbabilityTheory
