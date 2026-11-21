/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.Semimartingale.MeasureChange.GirsanovMeyer
public import StochLean.Probability.Process.Semimartingale.PredictableQuadraticCovariation.LocalMartingale
public import StochLean.Probability.Process.Semimartingale.QuadraticCovariation.EnvironmentInvariance

/-! # Predictable Girsanov theorem under equivalent measures

This file implements Protter III.40.  The predictable density covariation is
selected only on its actual locally-integrable-variation domain.  Its target
correction integrates the reverse density's left limit, retaining the
project's zero value for every process left limit at time zero.
-/

@[expose] public section

open MeasureTheory Filter
open scoped NNReal

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}
  {P Q : Measure Ω} [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
  {F : Filtration ℝ≥0 mΩ} {M : ℝ≥0 → Ω → ℝ}

/-- The predictable covariation `⟨Z,M⟩` selected as the canonical compensator
of the actual raw density covariation. -/
noncomputable def densityPredictableCovariation
    (hM : IsLocalMartingale M F P) (hF : F.IsUsual P)
    (hV : HasLocallyIntegrableVariation (densityRawCovariation (Q := Q) hM hF) F P) :
    ℝ≥0 → Ω → ℝ :=
  let hZ := (isLocalMartingale_densityProcess (Q := Q) hF).isSemimartingale hF
  hZ.predictableQuadraticCovariation (hM.isSemimartingale hF) hF hV

/-- The selected predictable density covariation is strongly predictable,
everywhere càdlàg, exactly zero initially and locally of integrable variation;
subtracting it from the raw density covariation is a `P`-local martingale. -/
theorem densityPredictableCovariation_properties
    (hM : IsLocalMartingale M F P) (hF : F.IsUsual P)
    (hV : HasLocallyIntegrableVariation (densityRawCovariation (Q := Q) hM hF) F P) :
    let A := densityPredictableCovariation (Q := Q) hM hF hV
    IsStronglyPredictable F A ∧ (∀ ω, IsCadlagPath (A · ω)) ∧ A 0 = 0 ∧
      HasLocallyIntegrableVariation A F P ∧
      IsLocalMartingale (densityRawCovariation (Q := Q) hM hF - A) F P := by
  intro A
  exact ((isLocalMartingale_densityProcess (Q := Q) hF).isSemimartingale hF)
    |>.predictableQuadraticCovariation_properties (hM.isSemimartingale hF) hF hV

/-- Protter III.40 correction `∫ Z₋⁻¹ d⟨Z,M⟩`, expressed as the target-law
stochastic integral of the reverse canonical density's left limit. -/
noncomputable def predictableGirsanovCorrection
    (hM : IsLocalMartingale M F P) (hQP : Q ≪ P) (hPQ : P ≪ Q)
    (hF : F.IsUsual P)
    (hV : HasLocallyIntegrableVariation (densityRawCovariation (Q := Q) hM hF) F P) :
    ℝ≥0 → Ω → ℝ := by
  let A := densityPredictableCovariation (Q := Q) hM hF hV
  let hA := densityPredictableCovariation_properties (Q := Q) hM hF hV
  let hpA : IsStronglyPredictable F A := hA.1
  let hcA : ∀ ω, IsCadlagPath (A · ω) := hA.2.1
  let hvA : HasLocallyIntegrableVariation A F P := hA.2.2.2.1
  let hAP : IsSemimartingale A F P :=
    hvA.hasFiniteVariationPaths.isSemimartingale hpA.stronglyAdapted.adapted hF
      (Eventually.of_forall hcA)
  let hFQ : F.IsUsual Q := hF.of_absolutelyContinuous hPQ
  let hAQ : IsSemimartingale A F Q := hAP.absolutelyContinuous hQP hF
  let hWQ : IsLocalMartingale (densityProcess P Q F) F Q :=
    isLocalMartingale_densityProcess hFQ
  exact hAQ.stochasticIntegral hFQ
    (hWQ.1.leftLimitProcess_of_usual hFQ hWQ.2.1)
    hWQ.2.1.hasCagladPaths_leftLimitProcess

/-- On one target-full-measure event, the reverse density left limit used by
the correction is the reciprocal of the forward density left limit at every
strictly positive time.  Time zero remains excluded by the project convention. -/
theorem ae_forall_reverseDensity_leftLimit_eq_inv_under_target
    (hQP : Q ≪ P) (hPQ : P ≪ Q) (hF : F.IsUsual P) :
    ∀ᵐ ω ∂Q, ∀ t : ℝ≥0, 0 < t →
      leftLimitProcess (densityProcess P Q F) t ω =
        1 / leftLimitProcess (densityProcess Q P F) t ω :=
  hQP.ae_le (ae_forall_leftLimit_reverse_eq_inv_densityProcess hQP hPQ hF)

/-- The predictable correction starts at zero. -/
theorem predictableGirsanovCorrection_zero_ae
    (hM : IsLocalMartingale M F P) (hQP : Q ≪ P) (hPQ : P ≪ Q)
    (hF : F.IsUsual P)
    (hV : HasLocallyIntegrableVariation (densityRawCovariation (Q := Q) hM hF) F P) :
    predictableGirsanovCorrection (Q := Q) hM hQP hPQ hF hV 0 =ᵐ[Q] 0 := by
  let A := densityPredictableCovariation (Q := Q) hM hF hV
  let hA := densityPredictableCovariation_properties (Q := Q) hM hF hV
  let hpA : IsStronglyPredictable F A := hA.1
  let hcA : ∀ ω, IsCadlagPath (A · ω) := hA.2.1
  let hvA : HasLocallyIntegrableVariation A F P := hA.2.2.2.1
  let hAP : IsSemimartingale A F P :=
    hvA.hasFiniteVariationPaths.isSemimartingale hpA.stronglyAdapted.adapted hF
      (Eventually.of_forall hcA)
  let hFQ : F.IsUsual Q := hF.of_absolutelyContinuous hPQ
  let hAQ : IsSemimartingale A F Q := hAP.absolutelyContinuous hQP hF
  let hWQ : IsLocalMartingale (densityProcess P Q F) F Q :=
    isLocalMartingale_densityProcess hFQ
  let Wl := leftLimitProcess (densityProcess P Q F)
  let haWl : Adapted F Wl := hWQ.1.leftLimitProcess_of_usual hFQ hWQ.2.1
  let hrWl : HasCagladPaths Wl Q := hWQ.2.1.hasCagladPaths_leftLimitProcess
  have hzero := hAQ.stochasticIntegral_zero_ae hFQ haWl hrWl
  filter_upwards [hzero] with ω hω
  rw [predictableGirsanovCorrection]
  rw [hω]
  simp [Wl]

/-- The right-value companion of the predictable correction.  It adds the
raw target-law covariation `[W,⟨Z,M⟩]` to the left-value integral. -/
noncomputable def predictableGirsanovRightCorrection
    (hM : IsLocalMartingale M F P) (hQP : Q ≪ P) (hPQ : P ≪ Q)
    (hF : F.IsUsual P)
    (hV : HasLocallyIntegrableVariation (densityRawCovariation (Q := Q) hM hF) F P) :
    ℝ≥0 → Ω → ℝ := by
  let A := densityPredictableCovariation (Q := Q) hM hF hV
  let hA := densityPredictableCovariation_properties (Q := Q) hM hF hV
  let hpA : IsStronglyPredictable F A := hA.1
  let hcA : ∀ ω, IsCadlagPath (A · ω) := hA.2.1
  let hvA : HasLocallyIntegrableVariation A F P := hA.2.2.2.1
  let hAP : IsSemimartingale A F P :=
    hvA.hasFiniteVariationPaths.isSemimartingale hpA.stronglyAdapted.adapted hF
      (Eventually.of_forall hcA)
  let hFQ : F.IsUsual Q := hF.of_absolutelyContinuous hPQ
  let hAQ : IsSemimartingale A F Q := hAP.absolutelyContinuous hQP hF
  let hWQ : IsLocalMartingale (densityProcess P Q F) F Q :=
    isLocalMartingale_densityProcess hFQ
  exact predictableGirsanovCorrection hM hQP hPQ hF hV +
    (hWQ.isSemimartingale hFQ).quadraticCovariation hAQ hFQ

/-- The target-law right-value correction makes `M` a local martingale.  This
is the product-algebra core of III.40 before replacing the right-value process
by its predictable compensator. -/
theorem isLocalMartingale_sub_predictableGirsanovRightCorrection
    (hM : IsLocalMartingale M F P) (hQP : Q ≪ P) (hPQ : P ≪ Q)
    (hF : F.IsUsual P)
    (hV : HasLocallyIntegrableVariation (densityRawCovariation (Q := Q) hM hF) F P) :
    IsLocalMartingale
      (M - predictableGirsanovRightCorrection (Q := Q) hM hQP hPQ hF hV) F Q := by
  let Z := densityProcess Q P F
  let W := densityProcess P Q F
  let A := densityPredictableCovariation (Q := Q) hM hF hV
  obtain ⟨hpA, hcAall, _, hvA, _⟩ :=
    densityPredictableCovariation_properties hM hF hV
  let hFQ : F.IsUsual Q := hF.of_absolutelyContinuous hPQ
  let hZ : IsLocalMartingale Z F P := isLocalMartingale_densityProcess hF
  let hW : IsLocalMartingale W F Q := isLocalMartingale_densityProcess hFQ
  let hZP : IsSemimartingale Z F P := hZ.isSemimartingale hF
  let hMP : IsSemimartingale M F P := hM.isSemimartingale hF
  let hcAP : HasCadlagPaths A P := Eventually.of_forall hcAall
  let hcAQ : HasCadlagPaths A Q := Eventually.of_forall hcAall
  let hAP : IsSemimartingale A F P :=
    hvA.hasFiniteVariationPaths.isSemimartingale hpA.stronglyAdapted.adapted hF hcAP
  let hAQ : IsSemimartingale A F Q := hAP.absolutelyContinuous hQP hF
  let hWQ : IsSemimartingale W F Q := hW.isSemimartingale hFQ
  let hWP : IsSemimartingale W F P := hWQ.absolutelyContinuous hPQ hFQ
  let H := leftLimitProcess A
  let haH : Adapted F H := hAP.adapted.leftLimitProcess_of_usual hF hcAP
  let hrHP : HasCagladPaths H P := hcAP.hasCagladPaths_leftLimitProcess
  let hrHQ : HasCagladPaths H Q := hQP.ae_le hrHP
  let NP := hWP.stochasticIntegral hF haH hrHP
  let NQ := hWQ.stochasticIntegral hFQ haH hrHQ
  have hNQ : IsLocalMartingale NQ F Q :=
    hWQ.isLocalMartingale_stochasticIntegral hFQ hW haH hrHQ
  have heNPQ : Indistinguishable NP NQ Q := by
    have heP := hWQ.stochasticIntegral_absolutelyContinuous hPQ hFQ hF haH hrHQ
    filter_upwards [hQP.ae_le heP] with ω hω t
    change hWP.stochasticIntegral hF haH hrHP t ω =
      hWQ.stochasticIntegral hFQ haH hrHQ t ω
    exact hω t
  have hNP : IsLocalMartingale NP F Q :=
    hNQ.congr hFQ (hWP.adapted_stochasticIntegral hF haH hrHP) heNPQ.symm
  have hK : IsLocalMartingale (Z * M - A) F P := by
    simpa only [Z, A, densityPredictableCovariation] using
      hZ.isLocalMartingale_mul_sub_predictableQuadraticCovariation hM hF hV
  have hZNP : IsLocalMartingale (Z * NP) F P :=
    hNP.mul_densityProcess_of_equivalent hQP hPQ hF
  have hsum : IsLocalMartingale ((Z * M - A) + Z * NP) F P := hK.add hZNP hF
  let RP := W * A - NP
  let LP := M - RP
  have haRP : Adapted F RP := (hW.1.mul hAP.adapted).sub hNP.1
  have haLP : Adapted F LP := hM.1.sub haRP
  have hWZP : Indistinguishable (W * Z) (fun _ _ ↦ (1 : ℝ)) P :=
    densityProcess_reverse_mul_indistinguishable_one hQP hPQ hF
  have heZLP : Indistinguishable (Z * LP) ((Z * M - A) + Z * NP) P := by
    filter_upwards [hWZP] with ω hω t
    have hZW : Z t ω * W t ω = 1 := by
      simpa only [Pi.mul_apply, mul_comm] using hω t
    change Z t ω * (M t ω - (W t ω * A t ω - NP t ω)) =
      (Z t ω * M t ω - A t ω) + Z t ω * NP t ω
    calc
      Z t ω * (M t ω - (W t ω * A t ω - NP t ω)) =
          Z t ω * M t ω - (Z t ω * W t ω) * A t ω + Z t ω * NP t ω := by ring
      _ = (Z t ω * M t ω - A t ω) + Z t ω * NP t ω := by rw [hZW]; ring
  have hZLP : IsLocalMartingale (Z * LP) F P :=
    hsum.congr hF (hZ.1.mul haLP) heZLP.symm
  have hWZLP : IsLocalMartingale (W * (Z * LP)) F Q :=
    hZLP.mul_densityProcess_of_equivalent hPQ hQP hFQ
  have heLP : Indistinguishable (W * (Z * LP)) LP Q := by
    filter_upwards [hQP.ae_le hWZP] with ω hω t
    have hWZ : W t ω * Z t ω = 1 := by
      simpa only [Pi.mul_apply] using hω t
    change W t ω * (Z t ω * LP t ω) = LP t ω
    rw [← mul_assoc, hWZ, one_mul]
  have hLP : IsLocalMartingale LP F Q := hWZLP.congr hFQ haLP heLP
  let Wl := leftLimitProcess W
  let haWlP : Adapted F Wl := hWP.adapted.leftLimitProcess_of_usual hF hWP.hasCadlagPaths
  let hrWlP : HasCagladPaths Wl P := hWP.hasCadlagPaths.hasCagladPaths_leftLimitProcess
  let hrWlQ : HasCagladPaths Wl Q := hQP.ae_le hrWlP
  let JP := hAP.stochasticIntegral hF haWlP hrWlP
  let JQ := hAQ.stochasticIntegral hFQ haWlP hrWlQ
  let qP := hWP.quadraticCovariation hAP hF
  let qQ := hWQ.quadraticCovariation hAQ hFQ
  have hpartsP := hWP.integrationByParts hAP hF
  have heJ : Indistinguishable JQ JP Q := by
    simpa only [JP, JQ] using
      (hAP.stochasticIntegral_absolutelyContinuous hQP hF hFQ haWlP hrWlP)
  have heq : Indistinguishable qQ qP Q := by
    simpa only [qP, qQ] using
      (hWP.quadraticCovariation_absolutelyContinuous hAP hQP hF hFQ)
  have hJdef : predictableGirsanovCorrection (Q := Q) hM hQP hPQ hF hV = JQ := by
    rw [predictableGirsanovCorrection]
  have hRdef : predictableGirsanovRightCorrection (Q := Q) hM hQP hPQ hF hV =
      JQ + qQ := by
    rw [predictableGirsanovRightCorrection, hJdef]
  have heR : Indistinguishable
      (predictableGirsanovRightCorrection (Q := Q) hM hQP hPQ hF hV) RP Q := by
    filter_upwards [hQP.ae_le hpartsP, heJ, heq, heNPQ] with ω hp hJ hq hN t
    rw [hRdef]
    change JQ t ω + qQ t ω = W t ω * A t ω - NP t ω
    have hp' := hp t
    simp only [Pi.mul_apply, Pi.add_apply] at hp'
    rw [hJ t, hq t]
    linarith [hN t]
  have haRQ : Adapted F
      (predictableGirsanovRightCorrection (Q := Q) hM hQP hPQ hF hV) := by
    rw [hRdef]
    exact (hAQ.adapted_stochasticIntegral hFQ
      (hW.1.leftLimitProcess_of_usual hFQ hW.2.1)
      hW.2.1.hasCagladPaths_leftLimitProcess).add
        (hWQ.adapted_quadraticCovariation hAQ hFQ)
  have heFinal : Indistinguishable LP
      (M - predictableGirsanovRightCorrection (Q := Q) hM hQP hPQ hF hV) Q := by
    filter_upwards [heR] with ω hω t
    change M t ω - RP t ω =
      M t ω - predictableGirsanovRightCorrection (Q := Q) hM hQP hPQ hF hV t ω
    rw [hω t]
  exact hLP.congr hFQ (hM.1.sub haRQ) heFinal

/-- Protter III.40.  If the raw density covariation has locally integrable
variation, subtracting the reverse-left-density integral against its
predictable compensator produces a `Q`-local martingale. -/
theorem isLocalMartingale_sub_predictableGirsanovCorrection
    (hM : IsLocalMartingale M F P) (hQP : Q ≪ P) (hPQ : P ≪ Q)
    (hF : F.IsUsual P)
    (hV : HasLocallyIntegrableVariation (densityRawCovariation (Q := Q) hM hF) F P) :
    IsLocalMartingale
      (M - predictableGirsanovCorrection (Q := Q) hM hQP hPQ hF hV) F Q := by
  let A := densityPredictableCovariation (Q := Q) hM hF hV
  obtain ⟨hpA, hcAall, _, hvA, _⟩ :=
    densityPredictableCovariation_properties hM hF hV
  let hFQ : F.IsUsual Q := hF.of_absolutelyContinuous hPQ
  let hcAQ : HasCadlagPaths A Q := Eventually.of_forall hcAall
  let hvAQ : HasFiniteVariationPaths A Q := hQP.ae_le hvA.hasFiniteVariationPaths
  let hAQ : IsSemimartingale A F Q :=
    hvAQ.isSemimartingale hpA.stronglyAdapted.adapted hFQ hcAQ
  let hW : IsLocalMartingale (densityProcess P Q F) F Q :=
    isLocalMartingale_densityProcess hFQ
  let hWQ : IsSemimartingale (densityProcess P Q F) F Q := hW.isSemimartingale hFQ
  let Wl := leftLimitProcess (densityProcess P Q F)
  let haWl : Adapted F Wl := hW.1.leftLimitProcess_of_usual hFQ hW.2.1
  let hrWl : HasCagladPaths Wl Q := hW.2.1.hasCagladPaths_leftLimitProcess
  let J := hAQ.stochasticIntegral hFQ haWl hrWl
  let R := J + hWQ.quadraticCovariation hAQ hFQ
  have hJdef : predictableGirsanovCorrection (Q := Q) hM hQP hPQ hF hV = J := by
    rw [predictableGirsanovCorrection]
  have hRdef : predictableGirsanovRightCorrection (Q := Q) hM hQP hPQ hF hV = R := by
    rw [predictableGirsanovRightCorrection, hJdef]
  have haJ : Adapted F J := hAQ.adapted_stochasticIntegral hFQ haWl hrWl
  have hcJ : HasCadlagPaths J Q := hAQ.hasCadlagPaths_stochasticIntegral hFQ haWl hrWl
  have haq : Adapted F (hWQ.quadraticCovariation hAQ hFQ) :=
    hWQ.adapted_quadraticCovariation hAQ hFQ
  have hcq : HasCadlagPaths (hWQ.quadraticCovariation hAQ hFQ) Q :=
    hWQ.hasCadlagPaths_quadraticCovariation hAQ hFQ
  have haR : Adapted F R := haJ.add haq
  have hcR : HasCadlagPaths R Q := hcJ.add hcq
  let hvR := hW.hasLocallyIntegrableVariation_rightValueIntegral hpA hFQ hcAQ hvAQ
  let C := hvR.predictableCompensator haR hFQ hcR
  obtain ⟨_, _, _, _, hRC⟩ := hvR.predictableCompensator_properties haR hFQ hcR
  have hcomp : Indistinguishable C J Q := by
    simpa only [C, R, J] using
      (hW.predictableCompensator_rightValueIntegral hpA hFQ hcAQ hvAQ)
  have hRJ : IsLocalMartingale (R - J) F Q := by
    apply hRC.congr hFQ (haR.sub haJ)
    filter_upwards [hcomp] with ω hω t
    change R t ω - C t ω = R t ω - J t ω
    rw [hω t]
  have hMR : IsLocalMartingale (M - R) F Q := by
    rw [← hRdef]
    exact isLocalMartingale_sub_predictableGirsanovRightCorrection hM hQP hPQ hF hV
  apply (hMR.add hRJ hFQ).congr hFQ (hM.1.sub haJ)
  exact Eventually.of_forall fun ω t ↦ by
    change (M t ω - R t ω) + (R t ω - J t ω) = M t ω - J t ω
    ring

end ProbabilityTheory
