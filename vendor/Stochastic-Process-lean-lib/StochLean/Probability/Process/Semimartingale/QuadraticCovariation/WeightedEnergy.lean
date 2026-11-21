/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.Semimartingale.QuadraticCovariation.StieltjesRealization

/-! # Measurable raw bracket energies, including time zero

Weights are jointly measurable, not necessarily adapted. These extended
nonnegative integrals are not totalized real integrals. The initial values
belong to the original processes, independently of the chosen null-event versions.
-/

@[expose] public section

open MeasureTheory StochLean Set
open scoped NNReal ENNReal

namespace ProbabilityTheory.SemimartingaleBracketRealization

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsFiniteMeasure P]
  {F : Filtration ℝ≥0 mΩ} {X Y : ℝ≥0 → Ω → ℝ}
  {hX : IsSemimartingale X F P} {hY : IsSemimartingale Y F P} {hF : F.IsUsual P}
  (D : SemimartingaleBracketRealization hX hY hF)

noncomputable def weightedVariation (f g : Ω × ℝ≥0 → ℝ≥0∞) (ω : Ω) : ℝ≥0∞ :=
  ((‖X 0 ω‖₊ * ‖Y 0 ω‖₊ : ℝ≥0) : ℝ≥0∞) * (f (ω, 0) * g (ω, 0)) +
    ∫⁻ t, f (ω, t) * g (ω, t) ∂(D.variation ω).measure

noncomputable def leftEnergy (f : Ω × ℝ≥0 → ℝ≥0∞) (ω : Ω) : ℝ≥0∞ :=
  ((‖X 0 ω‖₊ ^ 2 : ℝ≥0) : ℝ≥0∞) * (f (ω, 0)) ^ 2 +
    ∫⁻ t, (f (ω, t)) ^ 2 ∂(D.left ω).measure

noncomputable def rightEnergy (g : Ω × ℝ≥0 → ℝ≥0∞) (ω : Ω) : ℝ≥0∞ :=
  ((‖Y 0 ω‖₊ ^ 2 : ℝ≥0) : ℝ≥0∞) * (g (ω, 0)) ^ 2 +
    ∫⁻ t, (g (ω, t)) ^ 2 ∂(D.right ω).measure

theorem measurable_weightedVariation {f g : Ω × ℝ≥0 → ℝ≥0∞}
    (hf : Measurable f) (hg : Measurable g) : Measurable (D.weightedVariation f g) := by
  have hx := ((hX.adapted 0).mono (F.le 0) le_rfl).nnnorm
  have hy := ((hY.adapted 0).mono (F.le 0) le_rfl).nnnorm
  exact ((hx.mul hy).coe_nnreal_ennreal.mul
    ((hf.comp measurable_prodMk_right).mul (hg.comp measurable_prodMk_right))).add
    (D.measurable_variation_lintegral (hf.mul hg))

theorem measurable_leftEnergy {f : Ω × ℝ≥0 → ℝ≥0∞}
    (hf : Measurable f) : Measurable (D.leftEnergy f) := by
  have hx := ((hX.adapted 0).mono (F.le 0) le_rfl).nnnorm
  exact ((hx.pow_const 2).coe_nnreal_ennreal.mul
    ((hf.comp measurable_prodMk_right).pow_const 2)).add
    (D.measurable_left_lintegral (hf.pow_const 2))

theorem measurable_rightEnergy {g : Ω × ℝ≥0 → ℝ≥0∞}
    (hg : Measurable g) : Measurable (D.rightEnergy g) := by
  have hy := ((hY.adapted 0).mono (F.le 0) le_rfl).nnnorm
  exact ((hy.pow_const 2).coe_nnreal_ennreal.mul
    ((hg.comp measurable_prodMk_right).pow_const 2)).add
    (D.measurable_right_lintegral (hg.pow_const 2))

theorem weightedVariation_le_sqrt_mul {f g : Ω × ℝ≥0 → ℝ≥0∞}
    (hf : Measurable f) (hg : Measurable g) :
    ∀ᵐ ω ∂P, D.weightedVariation f g ω ≤
      (D.leftEnergy f ω) ^ (1 / 2 : ℝ) * (D.rightEnergy g ω) ^ (1 / 2 : ℝ) := by
  filter_upwards [D.increment_bound] with ω hinc
  exact stieltjes_lintegral_mul_le_with_initial_atom (D.mixed_bv ω) (D.mixed_rc ω)
    (D.left ω) (D.right ω) hinc ‖X 0 ω‖₊ ‖Y 0 ω‖₊
    (hf.comp measurable_prodMk_left) (hg.comp measurable_prodMk_left)

theorem stieltjes_measures_eq_ae (E : SemimartingaleBracketRealization hX hY hF) :
    ∀ᵐ ω ∂P, (D.variation ω).measure = (E.variation ω).measure ∧
      (D.left ω).measure = (E.left ω).measure ∧ (D.right ω).measure = (E.right ω).measure := by
  filter_upwards [D.mixed_eq, E.mixed_eq, D.left_eq, E.left_eq, D.right_eq, E.right_eq]
    with ω hDA hEA hDB hEB hDC hEC
  have ha : (fun t ↦ D.mixed t ω) = (fun t ↦ E.mixed t ω) :=
    funext fun t ↦ (hDA t).symm.trans (hEA t)
  have hv : D.variation ω = E.variation ω := by
    apply StieltjesFunction.ext
    intro t
    change pathTotalVariation (fun u ↦ D.mixed u ω) t =
      pathTotalVariation (fun u ↦ E.mixed u ω) t
    rw [ha]
  have hb : D.left ω = E.left ω :=
    StieltjesFunction.ext fun t ↦ (hDB t).symm.trans (hEB t)
  have hc : D.right ω = E.right ω :=
    StieltjesFunction.ext fun t ↦ (hDC t).symm.trans (hEC t)
  exact ⟨by rw [hv], by rw [hb], by rw [hc]⟩

theorem weighted_energies_eq_ae (E : SemimartingaleBracketRealization hX hY hF)
    (f g : Ω × ℝ≥0 → ℝ≥0∞) :
    ∀ᵐ ω ∂P, D.weightedVariation f g ω = E.weightedVariation f g ω ∧
      D.leftEnergy f ω = E.leftEnergy f ω ∧ D.rightEnergy g ω = E.rightEnergy g ω := by
  filter_upwards [D.stieltjes_measures_eq_ae E] with ω hω
  simp only [weightedVariation, leftEnergy, rightEnergy, hω.1, hω.2.1, hω.2.2, and_self]

end ProbabilityTheory.SemimartingaleBracketRealization
