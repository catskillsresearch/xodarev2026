/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.Semimartingale.PredictableQuadraticCovariation
public import StochLean.Probability.Process.Semimartingale.PredictableQuadraticVariation.LocallySquareIntegrable
public import StochLean.Probability.Process.Semimartingale.QuadraticCovariation.KunitaWatanabe
public import StochLean.Probability.Process.Semimartingale.QuadraticCovariation.Stopping

/-! # The actual locally integrable variation domain of mixed brackets

The existing Kunita--Watanabe compact-interval variation estimate and the
arithmetic-geometric mean inequality bound mixed total variation by half
the sum of the two square-bracket total variations. Finiteness is proved
before real conversion, and usual cadlag adaptedness supplies measurability
of the actual variation, not merely a measurable dominating bound.

The minimum of native localizing sequences therefore gives the mixed
domain. The existing unmasked stopped-variation criterion is legitimate
even at zero lifetime, where every stopped path is constant. Actual raw
bracket stopping identities transfer the variation statements; the initial
product is neither removed nor assumed integrable.

Native locally-L2 martingales enter this domain through the already proved
square-bracket domain theorem. The resulting mixed angle is the existing
canonical predictable compensator, with no new selection or predicate.
-/

@[expose] public section

open MeasureTheory StochLean Filter Set
open scoped NNReal ENNReal

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
  {F : Filtration ℝ≥0 mΩ} {X Y M N : ℝ≥0 → Ω → ℝ}

private theorem integrableVariation_quadraticCovariation_of_square_variations
    (hX : IsSemimartingale X F P) (hY : IsSemimartingale Y F P) (hF : F.IsUsual P)
    (hQX : HasIntegrableVariation (hX.quadraticVariation hF) P)
    (hQY : HasIntegrableVariation (hY.quadraticVariation hF) P) :
    HasIntegrableVariation (hX.quadraticCovariation hY hF) P := by
  let V : Ω → ℝ := fun ω ↦
    ((eVariationOn (fun t ↦ hX.quadraticVariation hF t ω) univ).toReal +
      (eVariationOn (fun t ↦ hY.quadraticVariation hF t ω) univ).toReal) / 2
  have hV (ω : Ω) : 0 ≤ V ω := by dsimp [V]; positivity
  have hiV : Integrable V P :=
    (hQX.integrable_eVariationOn_toReal.add hQY.integrable_eVariationOn_toReal).div_const 2
  have hbound : ∀ᵐ ω ∂P,
      eVariationOn (fun t ↦ hX.quadraticCovariation hY hF t ω) univ ≤
        ENNReal.ofReal (V ω) := by
    filter_upwards [hX.eVariationOn_quadraticCovariation_le hY hF,
      hX.hasMonotonePaths_quadraticVariation hF, hY.hasMonotonePaths_quadraticVariation hF,
      hQX.ae_forall_norm_sub_le, hQY.ae_forall_norm_sub_le] with ω hkw hx hy hvx hvy
    rw [eVariationOn_univ_eq_iSup_Icc_nat]
    refine iSup_le fun n ↦ (hkw 0 n).trans (ENNReal.ofReal_le_ofReal ?_)
    have hnx := le_trans
      (le_abs_self (hX.quadraticVariation hF n ω - hX.quadraticVariation hF 0 ω))
      (by simpa only [Real.norm_eq_abs] using hvx 0 n)
    have hny := le_trans
      (le_abs_self (hY.quadraticVariation hF n ω - hY.quadraticVariation hF 0 ω))
      (by simpa only [Real.norm_eq_abs] using hvy 0 n)
    have hsx := Real.sq_sqrt (sub_nonneg.mpr (hx (bot_le : (0 : ℝ≥0) ≤ n)))
    have hsy := Real.sq_sqrt (sub_nonneg.mpr (hy (bot_le : (0 : ℝ≥0) ≤ n)))
    simp only [bot_eq_zero] at hsx hsy
    dsimp [V]
    nlinarith [sq_nonneg
      (Real.sqrt (hX.quadraticVariation hF n ω - hX.quadraticVariation hF 0 ω) -
        Real.sqrt (hY.quadraticVariation hF n ω - hY.quadraticVariation hF 0 ω))]
  refine ⟨hbound.mono fun _ hω ↦ ne_top_of_le_ne_top ENNReal.ofReal_ne_top hω, ?_⟩
  apply hiV.mono'
    ((hX.adapted_quadraticCovariation hY hF).measurable_eVariationOn_univ_of_usual hF
      (hX.hasCadlagPaths_quadraticCovariation hY hF)).ennreal_toReal.aestronglyMeasurable
  filter_upwards [hbound] with ω hω
  rw [Real.norm_of_nonneg ENNReal.toReal_nonneg]
  simpa only [ENNReal.toReal_ofReal (hV ω)] using
    ENNReal.toReal_mono ENNReal.ofReal_ne_top hω

namespace IsSemimartingale

/-- Locally integrable variation of the two actual raw square brackets
implies locally integrable variation of their actual raw mixed bracket. -/
theorem hasLocallyIntegrableVariation_quadraticCovariation
    (hX : IsSemimartingale X F P) (hY : IsSemimartingale Y F P) (hF : F.IsUsual P)
    (hQX : HasLocallyIntegrableVariation (hX.quadraticVariation hF) F P)
    (hQY : HasLocallyIntegrableVariation (hY.quadraticVariation hF) F P) :
    HasLocallyIntegrableVariation (hX.quadraticCovariation hY hF) F P := by
  obtain ⟨τ, hτ, hvX⟩ := hasLocallyIntegrableVariation_iff_exists_stopped.mp hQX
  obtain ⟨σ, hσ, hvY⟩ := hasLocallyIntegrableVariation_iff_exists_stopped.mp hQY
  have hρ := hτ.min hσ
  refine hasLocallyIntegrableVariation_iff_exists_stopped.mpr
    ⟨min τ σ, hρ, fun n ↦ ?_⟩
  have haτ : Adapted F (MeasureTheory.stoppedProcess (hX.quadraticVariation hF) (τ n)) :=
    ((hX.adapted_quadraticVariation hF).stronglyAdapted.stoppedProcess_of_usual hF
      (hX.hasCadlagPaths_quadraticVariation hF).hasRightContinuousPaths
      (hτ.isStoppingTime n)).adapted
  have haσ : Adapted F (MeasureTheory.stoppedProcess (hY.quadraticVariation hF) (σ n)) :=
    ((hY.adapted_quadraticVariation hF).stronglyAdapted.stoppedProcess_of_usual hF
      (hY.hasCadlagPaths_quadraticVariation hF).hasRightContinuousPaths
      (hσ.isStoppingTime n)).adapted
  have hx := (hvX n).stoppedProcess haτ hF
    ((hX.hasCadlagPaths_quadraticVariation hF).stoppedProcess (τ n)) (hσ.isStoppingTime n)
  have hy := (hvY n).stoppedProcess haσ hF
    ((hY.hasCadlagPaths_quadraticVariation hF).stoppedProcess (σ n)) (hτ.isStoppingTime n)
  have heX : σ n ⊓ τ n = (min τ σ) n := by
    funext ω
    exact min_comm (σ n ω) (τ n ω)
  have heY : τ n ⊓ σ n = (min τ σ) n := rfl
  rw [stoppedProcess_stoppedProcess, heX] at hx
  rw [stoppedProcess_stoppedProcess, heY] at hy
  have hx' := hx.congr (hX.quadraticVariation_stoppedProcess hF (hρ.isStoppingTime n)).symm
  have hy' := hy.congr (hY.quadraticVariation_stoppedProcess hF (hρ.isStoppingTime n)).symm
  have hxy := integrableVariation_quadraticCovariation_of_square_variations
    (hX.stoppedProcess hF (hρ.isStoppingTime n))
    (hY.stoppedProcess hF (hρ.isStoppingTime n)) hF hx' hy'
  exact hxy.congr (hX.quadraticCovariation_stoppedProcess_both hY hF (hρ.isStoppingTime n))

end IsSemimartingale

namespace IsLocalMartingale

/-- Native locally-L2 hypotheses establish the actual mixed bracket's
domain, without any initial-value moment hypothesis on either process. -/
theorem hasLocallyIntegrableVariation_quadraticCovariation_of_locally_squareIntegrable
    (hM : IsLocalMartingale M F P) (hN : IsLocalMartingale N F P) (hF : F.IsUsual P)
    (hLM : Locally (fun Z ↦ IsSquareIntegrableMartingale Z F P) F M P)
    (hLN : Locally (fun Z ↦ IsSquareIntegrableMartingale Z F P) F N P) :
    HasLocallyIntegrableVariation
      ((hM.isSemimartingale hF).quadraticCovariation (hN.isSemimartingale hF) hF) F P :=
  (hM.isSemimartingale hF).hasLocallyIntegrableVariation_quadraticCovariation
    (hN.isSemimartingale hF) hF
    (hM.hasLocallyIntegrableVariation_quadraticVariation_of_locally_squareIntegrable hF hLM)
    (hN.hasLocallyIntegrableVariation_quadraticVariation_of_locally_squareIntegrable hF hLN)

/-- Native locally-L2 martingales have the actual selected mixed angle
process. This constructs its legal domain before using the existing selector. -/
theorem exists_predictableQuadraticCovariation_of_locally_squareIntegrable
    (hM : IsLocalMartingale M F P) (hN : IsLocalMartingale N F P) (hF : F.IsUsual P)
    (hLM : Locally (fun Z ↦ IsSquareIntegrableMartingale Z F P) F M P)
    (hLN : Locally (fun Z ↦ IsSquareIntegrableMartingale Z F P) F N P) :
    ∃ hQ : HasLocallyIntegrableVariation
        ((hM.isSemimartingale hF).quadraticCovariation (hN.isSemimartingale hF) hF) F P,
      let A := (hM.isSemimartingale hF).predictableQuadraticCovariation
        (hN.isSemimartingale hF) hF hQ
      IsStronglyPredictable F A ∧ (∀ ω, IsCadlagPath (A · ω)) ∧ A 0 = 0 ∧
        HasLocallyIntegrableVariation A F P ∧
        IsLocalMartingale
          ((hM.isSemimartingale hF).quadraticCovariation (hN.isSemimartingale hF) hF - A) F P := by
  have hQ := hM.hasLocallyIntegrableVariation_quadraticCovariation_of_locally_squareIntegrable
    hN hF hLM hLN
  exact ⟨hQ, (hM.isSemimartingale hF).predictableQuadraticCovariation_properties
    (hN.isSemimartingale hF) hF hQ⟩

end IsLocalMartingale

end ProbabilityTheory
