/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.FiniteVariation.PredictableIntegralCompensator
public import StochLean.Probability.Process.FiniteVariation.SpecialLocalIntegrability
public import StochLean.Probability.Process.FiniteVariation.Yoeurp
public import StochLean.Probability.Process.Semimartingale.StochasticIntegral.FiniteVariation
public import StochLean.Probability.Process.Semimartingale.QuadraticCovariation.PureJump
public import StochLean.Analysis.PathVariation.CadlagIntegrandJumpCorrection

/-! # The corrected right-value compensator identity

For a native local martingale `M` and an actual predictable cadlag FV process
`A`, let `J` be the existing Chapter II integral of `M_-` against `A`. The
literal process `J + [M,A]` has locally integrable variation. Its canonical
compensator is indistinguishable from `J`, proved through an actual predictable
version of `J` and full compensator uniqueness.

The same literal expression equals the pathwise right-value Stieltjes integral
on one common event. The process left limit at zero is zero, whereas the
native path left limit at zero is `M_0`. Accordingly `J_0 = 0` and the raw
covariation retains `M_0 A_0`: no additional initial subtraction is made.

This corrects the predictable-integrator domain of Protter III.20 and extends
its bounded-martingale/integrable-variation hypotheses by native localization.
No initial moment, new right-integral selector, or product of random L1 bounds
is assumed.
-/

@[expose] public section

open MeasureTheory StochLean Filter Set
open scoped NNReal

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
  {F : Filtration ℝ≥0 mΩ} {M A : ℝ≥0 → Ω → ℝ}

/-- The actual right-value expression has locally integrable variation.
The bracket's local integrability follows from its actual local-martingale
property and FV paths, not from multiplying random integrable envelopes. -/
theorem IsLocalMartingale.hasLocallyIntegrableVariation_rightValueIntegral
    (hM : IsLocalMartingale M F P) (hpA : IsStronglyPredictable F A)
    (hF : F.IsUsual P) (hcA : HasCadlagPaths A P) (hvA : HasFiniteVariationPaths A P) :
    let hSM := hM.isSemimartingale hF
    let hSA := hvA.isSemimartingale hpA.stronglyAdapted.adapted hF hcA
    let haL := hM.1.leftLimitProcess_of_usual hF hM.2.1
    let hrL := hM.2.1.hasCagladPaths_leftLimitProcess
    HasLocallyIntegrableVariation
      (hSA.stochasticIntegral hF haL hrL + hSM.quadraticCovariation hSA hF) F P := by
  intro hSM hSA haL hrL
  have hvJ := hSA.hasLocallyIntegrableVariation_stochasticIntegral_of_predictable
    hpA hF hvA haL hrL
  have hQ := hpA.isLocalMartingale_quadraticCovariation hF hcA hvA hM
  have hvQ := hQ.hasLocallyIntegrableVariation_of_finiteVariation hF
    (hSM.hasFiniteVariationPaths_quadraticCovariation hSA hF)
  exact hvJ.add hvQ (hSA.adapted_stochasticIntegral hF haL hrL)
    (hSM.adapted_quadraticCovariation hSA hF) hF
    (hSA.hasCadlagPaths_stochasticIntegral hF haL hrL)
    (hSM.hasCadlagPaths_quadraticCovariation hSA hF)

/-- The canonical compensator of the actual right-value expression is the
actual left-value integral, up to indistinguishability. A genuine predictable
version is constructed before invoking full uniqueness. -/
theorem IsLocalMartingale.predictableCompensator_rightValueIntegral
    (hM : IsLocalMartingale M F P) (hpA : IsStronglyPredictable F A)
    (hF : F.IsUsual P) (hcA : HasCadlagPaths A P) (hvA : HasFiniteVariationPaths A P) :
    let hSM := hM.isSemimartingale hF
    let hSA := hvA.isSemimartingale hpA.stronglyAdapted.adapted hF hcA
    let haL := hM.1.leftLimitProcess_of_usual hF hM.2.1
    let hrL := hM.2.1.hasCagladPaths_leftLimitProcess
    let hvR := hM.hasLocallyIntegrableVariation_rightValueIntegral hpA hF hcA hvA
    Indistinguishable
      (hvR.predictableCompensator
        ((hSA.adapted_stochasticIntegral hF haL hrL).add
          (hSM.adapted_quadraticCovariation hSA hF)) hF
        ((hSA.hasCadlagPaths_stochasticIntegral hF haL hrL).add
          (hSM.hasCadlagPaths_quadraticCovariation hSA hF)))
      (hSA.stochasticIntegral hF haL hrL) P := by
  intro hSM hSA haL hrL hvR
  let J := hSA.stochasticIntegral hF haL hrL
  let Q := hSM.quadraticCovariation hSA hF
  have haJ : Adapted F J := hSA.adapted_stochasticIntegral hF haL hrL
  have hcJ : HasCadlagPaths J P := hSA.hasCadlagPaths_stochasticIntegral hF haL hrL
  have haQ : Adapted F Q := hSM.adapted_quadraticCovariation hSA hF
  have hcQ : HasCadlagPaths Q P := hSM.hasCadlagPaths_quadraticCovariation hSA hF
  obtain ⟨B, he, hpB, _⟩ :=
    hSA.exists_predictable_stochasticIntegral_of_predictable hpA hF haL hrL
  have hvB : HasFiniteVariationPaths B P :=
    (hSA.hasFiniteVariationPaths_stochasticIntegral hF hvA haL hrL).congr he
  have hB0 : B 0 =ᵐ[P] 0 := by
    filter_upwards [he, hSA.stochasticIntegral_zero_ae hF haL hrL] with ω hω h0
    rw [← hω 0, h0]
    simp only [leftLimitProcess_zero, Pi.zero_apply, zero_mul]
  have hQ : IsLocalMartingale Q F P :=
    hpA.isLocalMartingale_quadraticCovariation hF hcA hvA hM
  have hres : IsLocalMartingale (J + Q - B) F P := by
    apply hQ.congr hF ((haJ.add haQ).sub hpB.stronglyAdapted.adapted)
    filter_upwards [he] with ω hω t
    change Q t ω = J t ω + Q t ω - B t ω
    rw [show J t ω = B t ω from hω t]
    ring
  exact (hvR.predictableCompensator_unique (haJ.add haQ) hF (hcJ.add hcQ)
    hpB hvB hB0 hres).trans he.symm

private theorem pathStieltjesIntegral_leftLimitProcess_add_initial
    (M A : ℝ≥0 → Ω → ℝ) (ω : Ω)
    (hv : LocallyBoundedVariationOn (A · ω) univ) (hr : IsRightContinuousPath (A · ω))
    (T : ℝ≥0) :
    pathStieltjesIntegral (A · ω) hv hr (leftLimitProcess M · ω) T + M 0 ω * A 0 ω =
      pathStieltjesIntegral (A · ω) hv hr (Function.leftLim (M · ω)) T := by
  have he : pathStieltjesIncrementIntegral (A · ω) hv hr (leftLimitProcess M · ω) 0 T =
      pathStieltjesIncrementIntegral (A · ω) hv hr (Function.leftLim (M · ω)) 0 T := by
    apply pathStieltjesIncrementIntegral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    simp only [leftLimitProcess, if_neg ht.1.ne']
  simp only [pathStieltjesIntegral, leftLimitProcess_zero, Pi.zero_apply, zero_mul,
    zero_add, he, leftLim_eq_of_isBot (show IsBot (0 : ℝ≥0) from fun _ ↦ bot_le)]
  exact add_comm _ _

namespace IsSemimartingale

/-- On the original common-AE FV paths, the literal left integral plus raw
covariation is the right-value pathwise integral. This path identity needs
neither predictability of the FV source nor a martingale hypothesis. -/
theorem stochasticIntegral_leftLimit_add_quadraticCovariation_eq_pathStieltjesIntegral_ae
    (hM : IsSemimartingale M F P) (hA : IsSemimartingale A F P) (hF : F.IsUsual P)
    (hvA : HasFiniteVariationPaths A P) :
    let haL := hM.adapted.leftLimitProcess_of_usual hF hM.hasCadlagPaths
    let hrL := hM.hasCadlagPaths.hasCagladPaths_leftLimitProcess
    ∀ᵐ ω ∂P, ∃ hv : LocallyBoundedVariationOn (A · ω) univ,
      ∃ hr : IsCadlagPath (A · ω), ∀ t,
        hA.stochasticIntegral hF haL hrL t ω + hM.quadraticCovariation hA hF t ω =
          pathStieltjesIntegral (A · ω) hv hr.1 (M · ω) t := by
  intro haL hrL
  filter_upwards [hA.stochasticIntegral_eq_pathStieltjesIntegral_ae hF hvA haL hrL,
    hM.quadraticCovariation_of_finiteVariation_right hA hF hvA, hM.hasCadlagPaths]
    with ω hi hq hm
  obtain ⟨hv, hr, hi⟩ := hi
  refine ⟨hv, hr, fun t ↦ ?_⟩
  rw [hi t, hq t]
  have he := pathStieltjesIntegral_sub_leftLim_integrand_eq_tsum hv hr.1 hm t
  have h0 := pathStieltjesIntegral_leftLimitProcess_add_initial M A ω hv hr.1 t
  have hs : (∑' s : Ioc 0 t, jumpProcess M s ω * jumpProcess A s ω) =
      ∑' s : Ioc 0 t, (M s ω - Function.leftLim (M · ω) s) *
        (A s ω - Function.leftLim (A · ω) s) := by
    apply tsum_congr
    intro s
    simp only [jumpProcess, Pi.sub_apply, leftLimitProcess, if_neg s.property.1.ne']
  rw [hs]
  linarith

end IsSemimartingale
end ProbabilityTheory
