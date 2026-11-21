/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.Semimartingale.Complex.Basic
public import StochLean.Probability.Process.Semimartingale.QuadraticCovariation.ContinuousPart

/-! # Complex bilinear square brackets and real nonnegative energy

These are algebraic combinations of the existing real bracket owners.
The complex bilinear bracket [Z,Z] and the real energy [Z,conj Z] are
different objects. Only the latter is asserted to be nonnegative/increasing.
-/

@[expose] public section

open MeasureTheory
open scoped NNReal

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsFiniteMeasure P]
  {F : Filtration ℝ≥0 mΩ} {Z : ℝ≥0 → Ω → ℂ}

noncomputable def IsComplexSemimartingale.quadraticVariation
    (hZ : IsComplexSemimartingale Z F P) (hF : F.IsUsual P) : ℝ≥0 → Ω → ℂ :=
  complexProcess (hZ.1.quadraticVariation hF - hZ.2.quadraticVariation hF)
    ((2 : ℝ) • hZ.1.quadraticCovariation hZ.2 hF)

noncomputable def IsComplexSemimartingale.continuousQuadraticVariation
    (hZ : IsComplexSemimartingale Z F P) (hF : F.IsUsual P) : ℝ≥0 → Ω → ℂ :=
  complexProcess (hZ.1.continuousQuadraticVariation hF - hZ.2.continuousQuadraticVariation hF)
    ((2 : ℝ) • hZ.1.continuousQuadraticCovariation hZ.2 hF)

noncomputable def IsComplexSemimartingale.quadraticEnergy
    (hZ : IsComplexSemimartingale Z F P) (hF : F.IsUsual P) : ℝ≥0 → Ω → ℝ :=
  hZ.1.quadraticVariation hF + hZ.2.quadraticVariation hF

noncomputable def IsComplexSemimartingale.continuousQuadraticEnergy
    (hZ : IsComplexSemimartingale Z F P) (hF : F.IsUsual P) : ℝ≥0 → Ω → ℝ :=
  hZ.1.continuousQuadraticVariation hF + hZ.2.continuousQuadraticVariation hF

theorem IsComplexSemimartingale.isComplexSemimartingale_quadraticVariation
    (hZ : IsComplexSemimartingale Z F P) (hF : F.IsUsual P) :
    IsComplexSemimartingale (hZ.quadraticVariation hF) F P :=
  ((hZ.1.isSemimartingale_quadraticVariation hF).sub
    (hZ.2.isSemimartingale_quadraticVariation hF)).complex
      ((hZ.1.isSemimartingale_quadraticCovariation hZ.2 hF).const_mul 2)

theorem IsComplexSemimartingale.isComplexSemimartingale_continuousQuadraticVariation
    (hZ : IsComplexSemimartingale Z F P) (hF : F.IsUsual P) :
    IsComplexSemimartingale (hZ.continuousQuadraticVariation hF) F P :=
  ((hZ.1.isSemimartingale_continuousQuadraticVariation hF).sub
    (hZ.2.isSemimartingale_continuousQuadraticVariation hF)).complex
      ((hZ.1.isSemimartingale_continuousQuadraticCovariation hZ.2 hF).const_mul 2)

theorem IsComplexSemimartingale.quadraticVariation_zero_ae
    (hZ : IsComplexSemimartingale Z F P) (hF : F.IsUsual P) :
    hZ.quadraticVariation hF 0 =ᵐ[P] fun ω ↦ (Z 0 ω) ^ 2 := by
  filter_upwards [hZ.1.quadraticVariation_zero_ae hF, hZ.2.quadraticVariation_zero_ae hF,
    hZ.1.quadraticCovariation_zero_ae hZ.2 hF] with ω hR hI hRI
  apply Complex.ext <;>
    simp only [quadraticVariation, complexProcess, Pi.sub_apply, Pi.smul_apply, smul_eq_mul,
      hR, hI, hRI, pow_two, Complex.mul_re, Complex.mul_im]
  ring

theorem IsComplexSemimartingale.continuousQuadraticVariation_zero
    (hZ : IsComplexSemimartingale Z F P) (hF : F.IsUsual P) (ω : Ω) :
    hZ.continuousQuadraticVariation hF 0 ω = 0 := by
  apply Complex.ext <;>
    simp [continuousQuadraticVariation, complexProcess,
      IsSemimartingale.continuousQuadraticVariation_zero,
      IsSemimartingale.continuousQuadraticCovariation_zero]

theorem IsComplexSemimartingale.hasMonotonePaths_quadraticEnergy
    (hZ : IsComplexSemimartingale Z F P) (hF : F.IsUsual P) :
    HasMonotonePaths (hZ.quadraticEnergy hF) P := by
  filter_upwards [hZ.1.hasMonotonePaths_quadraticVariation hF,
    hZ.2.hasMonotonePaths_quadraticVariation hF] with ω hR hI
  exact hR.add hI

theorem IsComplexSemimartingale.monotone_continuousQuadraticEnergy
    (hZ : IsComplexSemimartingale Z F P) (hF : F.IsUsual P) (ω : Ω) :
    Monotone (hZ.continuousQuadraticEnergy hF · ω) :=
  (hZ.1.monotone_continuousQuadraticVariation hF ω).add
    (hZ.2.monotone_continuousQuadraticVariation hF ω)

theorem IsComplexSemimartingale.quadraticEnergy_zero_ae
    (hZ : IsComplexSemimartingale Z F P) (hF : F.IsUsual P) :
    hZ.quadraticEnergy hF 0 =ᵐ[P] fun ω ↦ ‖Z 0 ω‖ ^ 2 := by
  filter_upwards [hZ.1.quadraticVariation_zero_ae hF, hZ.2.quadraticVariation_zero_ae hF]
    with ω hR hI
  simp only [quadraticEnergy, Pi.add_apply, hR, hI]
  rw [← Complex.normSq_eq_norm_sq]
  simp only [Complex.normSq_apply, pow_two]

theorem IsComplexSemimartingale.quadraticEnergy_nonneg
    (hZ : IsComplexSemimartingale Z F P) (hF : F.IsUsual P) :
    ∀ᵐ ω ∂P, ∀ t, 0 ≤ hZ.quadraticEnergy hF t ω := by
  filter_upwards [hZ.hasMonotonePaths_quadraticEnergy hF, hZ.quadraticEnergy_zero_ae hF]
    with ω hm h0 t
  exact (h0.symm ▸ sq_nonneg ‖Z 0 ω‖).trans (hm (show 0 ≤ t from bot_le))

theorem IsComplexSemimartingale.continuousQuadraticEnergy_zero
    (hZ : IsComplexSemimartingale Z F P) (hF : F.IsUsual P) (ω : Ω) :
    hZ.continuousQuadraticEnergy hF 0 ω = 0 := by
  simp only [continuousQuadraticEnergy, Pi.add_apply,
    IsSemimartingale.continuousQuadraticVariation_zero, add_zero]

theorem IsComplexSemimartingale.continuousQuadraticEnergy_nonneg
    (hZ : IsComplexSemimartingale Z F P) (hF : F.IsUsual P) (t : ℝ≥0) (ω : Ω) :
    0 ≤ hZ.continuousQuadraticEnergy hF t ω := by
  rw [← hZ.continuousQuadraticEnergy_zero hF ω]
  exact hZ.monotone_continuousQuadraticEnergy hF ω bot_le

end ProbabilityTheory
