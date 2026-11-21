/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.Semimartingale.MeasureChange.AbsoluteContinuousKillingResidual
public import StochLean.Probability.Process.Semimartingale.MeasureChange.AbsoluteContinuousMartingaleTransfer
public import StochLean.Probability.Process.Semimartingale.QuadraticCovariation.IntegrationByParts
public import StochLean.Probability.Process.Semimartingale.QuadraticCovariation.GeneralLocalMartingale
public import StochLean.Probability.Process.Semimartingale.StochasticIntegral.IntegratorAlgebra
public import StochLean.Probability.Process.FiniteVariation.Yoeurp

/-! # Lenglart--Girsanov theorem under one-way absolute continuity

The right-value raw-covariation correction alone misses the jump at which the
density dies from a positive left limit.  The predictable compensator of that
single killing jump supplies exactly the remaining term.  Multiplication by
the density reduces the target-law assertion to source local-martingale
algebra, while `AbsoluteContinuousKillingResidual` supplies the pathwise
extinction identity.
-/

@[expose] public section

open MeasureTheory StochLean Filter Set Function
open scoped NNReal Topology

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}
  {P Q : Measure Ω} [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
  {F : Filtration ℝ≥0 mΩ} {M : ℝ≥0 → Ω → ℝ}

/-- Protter III.42 (Lenglart--Girsanov).  Under `Q ≪ P`, subtracting the
right-value raw density-covariation correction and adding the predictable
compensator of the density-killing jump transforms every `P`-local martingale
into a `Q`-local martingale. -/
theorem isLocalMartingale_sub_absoluteContinuousRawGirsanovCorrection_add_killingCompensator
    (hM : IsLocalMartingale M F P) (hQP : Q ≪ P)
    (hFP : F.IsUsual P) (hFQ : F.IsUsual Q) :
    IsLocalMartingale
      (M - absoluteContinuousRawGirsanovCorrection hM hQP hFP hFQ +
        absoluteContinuousKillingJumpCompensator (Q := Q) hM hFP) F Q := by
  let Z := densityProcess Q P F
  let A := absoluteContinuousRawGirsanovCorrection hM hQP hFP hFQ
  let U := absoluteContinuousKillingJump Q P F M
  let C := absoluteContinuousKillingJumpCompensator (Q := Q) hM hFP
  let B := densityRawCovariation (Q := Q) hM hFP
  let hZ : IsLocalMartingale Z F P := isLocalMartingale_densityProcess hFP
  let hZP : IsSemimartingale Z F P := hZ.isSemimartingale hFP
  obtain ⟨haA, hcA, hvA, hAP⟩ :=
    absoluteContinuousRawGirsanovCorrection_source_properties hM hQP hFP hFQ
  obtain ⟨hpC, hcCall, hC0, hCliv, hUC⟩ :=
    absoluteContinuousKillingJumpCompensator_properties (Q := Q) hM hFP
  let hcC : HasCadlagPaths C P := Eventually.of_forall hcCall
  let hvC : HasFiniteVariationPaths C P := hCliv.hasFiniteVariationPaths
  let hCP : IsSemimartingale C F P :=
    hvC.isSemimartingale hpC.stronglyAdapted.adapted hFP hcC
  let hUliv := hasLocallyIntegrableVariation_absoluteContinuousKillingJump
    (Q := Q) hM hFP
  let haU := adapted_absoluteContinuousKillingJump (Q := Q) hM hFP
  let hcU := hasCadlagPaths_absoluteContinuousKillingJump
    (Q := Q) (P := P) (F := F) (M := M)
  let hUP : IsSemimartingale U F P :=
    hUliv.hasFiniteVariationPaths.isSemimartingale haU hFP hcU
  let Zl := leftLimitProcess Z
  let haZl : Adapted F Zl := hZP.adapted.leftLimitProcess_of_usual hFP hZP.hasCadlagPaths
  let hrZl : HasCagladPaths Zl P := hZP.hasCadlagPaths.hasCagladPaths_leftLimitProcess
  let Al := leftLimitProcess A
  let haAl : Adapted F Al := hAP.adapted.leftLimitProcess_of_usual hFP hAP.hasCadlagPaths
  let hrAl : HasCagladPaths Al P := hAP.hasCadlagPaths.hasCagladPaths_leftLimitProcess
  let Cl := leftLimitProcess C
  let haCl : Adapted F Cl := hCP.adapted.leftLimitProcess_of_usual hFP hCP.hasCadlagPaths
  let hrCl : HasCagladPaths Cl P := hCP.hasCadlagPaths.hasCagladPaths_leftLimitProcess
  let JA := hAP.stochasticIntegral hFP haZl hrZl
  let IA := hZP.stochasticIntegral hFP haAl hrAl
  let qZA := hZP.quadraticCovariation hAP hFP
  let JU := hUP.stochasticIntegral hFP haZl hrZl
  let JC := hCP.stochasticIntegral hFP haZl hrZl
  let IC := hZP.stochasticIntegral hFP haCl hrCl
  let qZC := hZP.quadraticCovariation hCP hFP
  have hIA : IsLocalMartingale IA F P := hZ.isLocalMartingale_stochasticIntegral hFP haAl hrAl
  have hIC : IsLocalMartingale IC F P := hZ.isLocalMartingale_stochasticIntegral hFP haCl hrCl
  have hqZC : IsLocalMartingale qZC F P := by
    simpa only [qZC, hZP, hCP] using
      hpC.isLocalMartingale_quadraticCovariation hFP hcC hvC hZ
  have hKA : IsLocalMartingale (Z * A - (JA + qZA)) F P := by
    have hparts : Indistinguishable (Z * A) (JA + IA + qZA) P := by
      simpa only [JA, IA, qZA, Zl, Al, haZl, hrZl, haAl, hrAl] using
        hZP.integrationByParts hAP hFP
    have he : Indistinguishable (Z * A - (JA + qZA)) IA P := by
      filter_upwards [hparts] with ω hω t
      have ht := hω t
      simp only [Pi.mul_apply, Pi.add_apply, Pi.sub_apply] at ht ⊢
      linarith
    have haKA : Adapted F (Z * A - (JA + qZA)) :=
      (hZ.1.mul haA).sub
        ((hAP.adapted_stochasticIntegral hFP haZl hrZl).add
          (hZP.adapted_quadraticCovariation hAP hFP))
    exact hIA.congr hFP haKA he.symm
  have hKC : IsLocalMartingale (Z * C - JC) F P := by
    have hparts : Indistinguishable (Z * C) (JC + IC + qZC) P := by
      simpa only [JC, IC, qZC, Zl, Cl, haZl, hrZl, haCl, hrCl] using
        hZP.integrationByParts hCP hFP
    have he : Indistinguishable (Z * C - JC) (IC + qZC) P := by
      filter_upwards [hparts] with ω hω t
      have ht := hω t
      simp only [Pi.mul_apply, Pi.add_apply, Pi.sub_apply] at ht ⊢
      linarith
    have haKC : Adapted F (Z * C - JC) :=
      (hZ.1.mul hpC.stronglyAdapted.adapted).sub
        (hCP.adapted_stochasticIntegral hFP haZl hrZl)
    exact (hIC.add hqZC hFP).congr hFP haKC he.symm
  let hUCP : IsSemimartingale (U - C) F P := hUP.sub hCP
  let JUC := hUCP.stochasticIntegral hFP haZl hrZl
  have hJUC : IsLocalMartingale JUC F P := by
    simpa only [JUC, hUCP] using hUC.isLocalMartingale_stochasticIntegral hFP haZl hrZl
  have hKCU : IsLocalMartingale (Z * C - JU) F P := by
    have heJUC : Indistinguishable JUC (JU - JC) P := by
      simpa only [JUC, hUCP, JU, JC] using
        hUP.stochasticIntegral_sub_integrator hCP hFP haZl hrZl
    have he : Indistinguishable ((Z * C - JC) - JUC) (Z * C - JU) P := by
      filter_upwards [heJUC] with ω hω t
      have ht := hω t
      simp only [Pi.mul_apply, Pi.sub_apply] at ht ⊢
      rw [ht]
      ring
    have haKCU : Adapted F (Z * C - JU) :=
      (hZ.1.mul hpC.stronglyAdapted.adapted).sub
        (hUP.adapted_stochasticIntegral hFP haZl hrZl)
    exact (hKC.sub hJUC hFP).congr hFP haKCU he
  have hK0 : IsLocalMartingale (Z * M - B) F P := by
    simpa only [Z, B, densityRawCovariation] using
      hZ.isLocalMartingale_mul_sub_quadraticCovariation hM hFP
  have hsource : IsLocalMartingale (Z * (M - A + C)) F P := by
    have hres : Indistinguishable (B - (JA + qZA) + JU) 0 P := by
      simpa only [Z, B, A, U, hZP, hAP, hUP, Zl, haZl, hrZl,
        JA, qZA, JU] using
        indistinguishable_absoluteContinuousRawGirsanovResidual_zero
          hM hQP hFP hFQ
    have he : Indistinguishable
        (((Z * M - B) - (Z * A - (JA + qZA))) + (Z * C - JU))
        (Z * (M - A + C)) P := by
      filter_upwards [hres] with ω hω t
      have ht := hω t
      simp only [Pi.mul_apply, Pi.sub_apply, Pi.add_apply, Pi.zero_apply] at ht ⊢
      linear_combination -ht
    have haSource : Adapted F (Z * (M - A + C)) :=
      hZ.1.mul ((hM.1.sub haA).add hpC.stronglyAdapted.adapted)
    exact ((hK0.sub hKA hFP).add hKCU hFP).congr hFP haSource he
  have haX : Adapted F (M - A + C) :=
    (hM.1.sub haA).add hpC.stronglyAdapted.adapted
  have hcX : HasCadlagPaths (M - A + C) P := (hM.2.1.sub hcA).add hcC
  exact hsource.of_mul_densityProcess_absolutelyContinuous haX hcX hQP hFP hFQ

end ProbabilityTheory
