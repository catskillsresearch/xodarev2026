/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.Semimartingale.PredictableQuadraticCovariation.LocallyIntegrable
public import StochLean.Probability.Process.FiniteVariation.CompensatorAlgebra
public import StochLean.Probability.Process.Semimartingale.QuadraticVariation.Algebra

/-! # Polarization of the actual predictable brackets

The actual two square domains first give the mixed domain by the existing
variation estimate, and then the square domain of the sum by raw polarization.
The canonical compensator's proved linearity transports that identity to
the actual selected angle processes. No third square-domain or candidate
mixed-angle hypothesis is supplied, and no initial product moment is needed.
-/

@[expose] public section

open MeasureTheory Filter
open scoped NNReal

namespace ProbabilityTheory.IsSemimartingale

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
  {F : Filtration ℝ≥0 mΩ} {X Y : ℝ≥0 → Ω → ℝ}

/-- The actual square-bracket domain is stable under addition of the sources. -/
theorem hasLocallyIntegrableVariation_quadraticVariation_add
    (hX : IsSemimartingale X F P) (hY : IsSemimartingale Y F P) (hF : F.IsUsual P)
    (hQX : HasLocallyIntegrableVariation (hX.quadraticVariation hF) F P)
    (hQY : HasLocallyIntegrableVariation (hY.quadraticVariation hF) F P) :
    HasLocallyIntegrableVariation ((hX.add hY).quadraticVariation hF) F P := by
  have hQC := hX.hasLocallyIntegrableVariation_quadraticCovariation hY hF hQX hQY
  have haX := hX.adapted_quadraticVariation hF
  have haY := hY.adapted_quadraticVariation hF
  have haC : Adapted F ((2 : ℝ) • hX.quadraticCovariation hY hF) :=
    fun t ↦ (hX.adapted_quadraticCovariation hY hF t).const_smul (2 : ℝ)
  have hcX := hX.hasCadlagPaths_quadraticVariation hF
  have hcY := hY.hasCadlagPaths_quadraticVariation hF
  have hcC : HasCadlagPaths ((2 : ℝ) • hX.quadraticCovariation hY hF) P :=
    (hX.hasCadlagPaths_quadraticCovariation hY hF).continuous_comp
      (continuous_const.mul continuous_id)
  exact ((hQX.add (hQC.smul 2) haX haC hF hcX hcC).add hQY
    (haX.add haC) haY hF (hcX.add hcC) hcY).congr (hX.quadraticVariation_add hY hF).symm

/-- Polarization identifies the already selected mixed angle from the three
actual selected square angles. The domain of the sum is derived, not assumed. -/
theorem predictableQuadraticCovariation_eq_polarization
    (hX : IsSemimartingale X F P) (hY : IsSemimartingale Y F P) (hF : F.IsUsual P)
    (hQX : HasLocallyIntegrableVariation (hX.quadraticVariation hF) F P)
    (hQY : HasLocallyIntegrableVariation (hY.quadraticVariation hF) F P) :
    let hQC := hX.hasLocallyIntegrableVariation_quadraticCovariation hY hF hQX hQY
    let hQS := hX.hasLocallyIntegrableVariation_quadraticVariation_add hY hF hQX hQY
    Indistinguishable (hX.predictableQuadraticCovariation hY hF hQC)
      (fun t ω ↦ ((hX.add hY).predictableQuadraticVariation hF hQS t ω -
        hX.predictableQuadraticVariation hF hQX t ω -
        hY.predictableQuadraticVariation hF hQY t ω) / 2) P := by
  let hQC := hX.hasLocallyIntegrableVariation_quadraticCovariation hY hF hQX hQY
  let hQS := hX.hasLocallyIntegrableVariation_quadraticVariation_add hY hF hQX hQY
  let QX := hX.quadraticVariation hF
  let QY := hY.quadraticVariation hF
  let QC := hX.quadraticCovariation hY hF
  let QS := (hX.add hY).quadraticVariation hF
  have haX := hX.adapted_quadraticVariation hF
  have haY := hY.adapted_quadraticVariation hF
  have haC := hX.adapted_quadraticCovariation hY hF
  have hcX := hX.hasCadlagPaths_quadraticVariation hF
  have hcY := hY.hasCadlagPaths_quadraticVariation hF
  have hcC := hX.hasCadlagPaths_quadraticCovariation hY hF
  have ha2 : Adapted F ((2 : ℝ) • QC) := fun t ↦ (haC t).const_smul (2 : ℝ)
  have hc2 : HasCadlagPaths ((2 : ℝ) • QC) P :=
    hcC.continuous_comp (continuous_const.mul continuous_id)
  have hvXC := hQX.add (hQC.smul 2) haX ha2 hF hcX hc2
  have hvR := hvXC.add hQY (haX.add ha2) haY hF (hcX.add hc2) hcY
  have heR := hQS.predictableCompensator_congr hvR
    ((hX.add hY).adapted_quadraticVariation hF) ((haX.add ha2).add haY) hF
    ((hX.add hY).hasCadlagPaths_quadraticVariation hF) ((hcX.add hc2).add hcY)
    (hX.quadraticVariation_add hY hF)
  have heSum := hvXC.predictableCompensator_add hQY (haX.add ha2) haY hF
    (hcX.add hc2) hcY
  have heXC := hQX.predictableCompensator_add (hQC.smul 2) haX ha2 hF hcX hc2
  have he2 := hQC.predictableCompensator_smul haC hF hcC 2
  filter_upwards [heR, heSum, heXC, he2] with ω hr hs hxc htwo t
  have h := (hr t).trans (hs t)
  simp only [Pi.add_apply, hxc t, htwo t, Pi.smul_apply, smul_eq_mul] at h
  change (hX.add hY).predictableQuadraticVariation hF hQS t ω =
    hX.predictableQuadraticVariation hF hQX t ω +
      2 * hX.predictableQuadraticCovariation hY hF hQC t ω +
      hY.predictableQuadraticVariation hF hQY t ω at h
  change hX.predictableQuadraticCovariation hY hF hQC t ω = _
  linarith

end ProbabilityTheory.IsSemimartingale
