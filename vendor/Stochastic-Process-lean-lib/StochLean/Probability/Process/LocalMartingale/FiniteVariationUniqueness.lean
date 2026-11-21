/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.LocalMartingale.ContinuousFiniteVariation
public import StochLean.Probability.Process.LocalMartingale.Congr
public import StochLean.ForMathlib.VariationAlgebra

/-! # Uniqueness from finite variation, jumps and local-martingale residuals

Identical positive-time jumps make the difference continuous. Its initial
value is checked separately, in accordance with the raw source convention.
-/

@[expose] public section

open MeasureTheory StochLean
open scoped NNReal

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsFiniteMeasure P]
  {F : Filtration ℝ≥0 mΩ} [SigmaFiniteFiltration P F] {X Z A B : ℝ≥0 → Ω → ℝ}

theorem IsLocalMartingale.indistinguishable_zero_of_finiteVariation_jump_zero
    (hX : IsLocalMartingale X F P) (hF : F.IsUsual P)
    (hv : HasFiniteVariationPaths X P)
    (hj : ∀ᵐ ω ∂P, ∀ t : ℝ≥0, t ≠ 0 → jumpProcess X t ω = 0)
    (h0 : X 0 =ᵐ[P] 0) : Indistinguishable X 0 P :=
  IsContinuousLocalMartingale.indistinguishable_zero_of_finiteVariation
    ⟨hX, hX.2.1.hasContinuousPaths_of_jumpProcess_eq_zero hj⟩ hF hv h0

theorem indistinguishable_of_finiteVariation_localMartingale_residuals
    (hF : F.IsUsual P) (haA : Adapted F A) (haB : Adapted F B)
    (hcA : HasCadlagPaths A P) (hcB : HasCadlagPaths B P)
    (hvA : HasFiniteVariationPaths A P) (hvB : HasFiniteVariationPaths B P)
    (hMA : IsLocalMartingale (Z - A) F P) (hMB : IsLocalMartingale (Z - B) F P)
    (hj : Indistinguishable (jumpProcess A) (jumpProcess B) P)
    (h0 : A 0 =ᵐ[P] B 0) : Indistinguishable A B P := by
  have he : Indistinguishable ((Z - B) - (Z - A)) (A - B) P := by
    apply ae_of_all
    intro ω t
    simp only [Pi.sub_apply]
    ring
  have hM := (hMB.sub hMA hF).congr hF (fun t ↦ (haA t).sub (haB t)) he
  have hv : HasFiniteVariationPaths (A - B) P := by
    filter_upwards [hvA, hvB] with ω ha hb
    exact locallyBoundedVariationOn_sub ha hb
  have hj0 : ∀ᵐ ω ∂P, ∀ t : ℝ≥0, t ≠ 0 → jumpProcess (A - B) t ω = 0 := by
    filter_upwards [hcA, hcB, hj] with ω ha hb heω t _
    rw [ha.jumpProcess_sub hb t, heω t, sub_self]
  have hz : (A - B) 0 =ᵐ[P] 0 := by
    filter_upwards [h0] with ω hω
    exact sub_eq_zero.mpr hω
  filter_upwards [hM.indistinguishable_zero_of_finiteVariation_jump_zero hF hv hj0 hz]
    with ω hω t
  exact sub_eq_zero.mp (hω t)

end ProbabilityTheory
