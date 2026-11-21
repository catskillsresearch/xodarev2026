/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.Semimartingale.QuadraticCovariation.WeightedEnergy
public import StochLean.ForMathlib.MeasureTheory.ExpectedCauchySchwarz

/-! # Protter II.25: the expectation/Lp corollary

For finite conjugate exponents, `(∫ B^(p/2))^(1/p)` is the extended Lp norm
of the square root of the energy `B`. Both L1/Linfinity endpoint inequalities
are included. Measurability is proved from joint measurability of the weights,
not assumed for the random energies. No adaptedness or finite-energy hypothesis
is imposed, and the raw initial terms are retained.
-/

@[expose] public section

open MeasureTheory StochLean
open scoped NNReal ENNReal

namespace ProbabilityTheory.SemimartingaleBracketRealization

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsFiniteMeasure P]
  {F : Filtration ℝ≥0 mΩ} {X Y : ℝ≥0 → Ω → ℝ}
  {hX : IsSemimartingale X F P} {hY : IsSemimartingale Y F P} {hF : F.IsUsual P}
  (D : SemimartingaleBracketRealization hX hY hF)

theorem expected_weightedVariation_le_Lp_mul_Lq
    {f g : Ω × ℝ≥0 → ℝ≥0∞} (hf : Measurable f) (hg : Measurable g)
    {p q : ℝ} (hpq : p.HolderConjugate q) :
    (∫⁻ ω, D.weightedVariation f g ω ∂P) ≤
      (∫⁻ ω, (D.leftEnergy f ω) ^ (p / 2) ∂P) ^ (1 / p) *
        (∫⁻ ω, (D.rightEnergy g ω) ^ (q / 2) ∂P) ^ (1 / q) :=
  lintegral_le_Lp_mul_Lq_of_ae_sqrt_mul (D.weightedVariation_le_sqrt_mul hf hg)
    (D.measurable_leftEnergy hf).aemeasurable (D.measurable_rightEnergy hg).aemeasurable hpq

theorem expected_weightedVariation_le_Linfty_mul_L1
    {f g : Ω × ℝ≥0 → ℝ≥0∞} (hf : Measurable f) (hg : Measurable g) :
    (∫⁻ ω, D.weightedVariation f g ω ∂P) ≤
      essSup (fun ω ↦ (D.leftEnergy f ω) ^ (1 / 2 : ℝ)) P *
        (∫⁻ ω, (D.rightEnergy g ω) ^ (1 / 2 : ℝ) ∂P) :=
  lintegral_le_Linfty_mul_L1_of_ae_sqrt_mul (D.weightedVariation_le_sqrt_mul hf hg)
    (D.measurable_rightEnergy hg).aemeasurable

theorem expected_weightedVariation_le_L1_mul_Linfty
    {f g : Ω × ℝ≥0 → ℝ≥0∞} (hf : Measurable f) (hg : Measurable g) :
    (∫⁻ ω, D.weightedVariation f g ω ∂P) ≤
      (∫⁻ ω, (D.leftEnergy f ω) ^ (1 / 2 : ℝ) ∂P) *
        essSup (fun ω ↦ (D.rightEnergy g ω) ^ (1 / 2 : ℝ)) P :=
  lintegral_le_L1_mul_Linfty_of_ae_sqrt_mul (D.weightedVariation_le_sqrt_mul hf hg)
    (D.measurable_leftEnergy hf).aemeasurable

theorem expected_weightedVariation_eq (E : SemimartingaleBracketRealization hX hY hF)
    (f g : Ω × ℝ≥0 → ℝ≥0∞) :
    (∫⁻ ω, D.weightedVariation f g ω ∂P) = (∫⁻ ω, E.weightedVariation f g ω ∂P) :=
  lintegral_congr_ae ((D.weighted_energies_eq_ae E f g).mono fun _ h ↦ h.1)

end ProbabilityTheory.SemimartingaleBracketRealization
