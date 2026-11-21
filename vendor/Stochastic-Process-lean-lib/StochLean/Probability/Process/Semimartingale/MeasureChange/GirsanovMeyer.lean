/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.Semimartingale.MeasureChange.MartingaleTransfer
public import StochLean.Probability.Process.Semimartingale.QuadraticCovariation.GeneralLocalMartingale
public import StochLean.Probability.Process.Semimartingale.StochasticIntegral.AbsoluteContinuity
public import StochLean.Probability.Process.FiniteVariation.RightValueCompensator

/-! # Equivalent-measure Girsanov--Meyer theorem

This file implements Protter III.39 with the raw quadratic covariation.  The
canonical correction is expressed without division by using the reverse
density process.  A later representation identifies it with the right-value
Stieltjes integral of the reverse density against the raw covariation.
-/

@[expose] public section

open MeasureTheory StochLean Filter
open scoped NNReal

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}
  {P Q : Measure Ω} [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
  {F : Filtration ℝ≥0 mΩ} {M : ℝ≥0 → Ω → ℝ}

/-- The canonical density process is a local martingale under its source law. -/
theorem isLocalMartingale_densityProcess (hF : F.IsUsual P) :
    IsLocalMartingale (densityProcess Q P F) F P :=
  (show IsUIMartingale (densityProcess Q P F) F P from
    ⟨martingale_densityProcess hF, uniformIntegrable_densityProcess hF⟩).isLocalMartingale
      hasCadlagPaths_densityProcess

/-- The raw covariation `[Z,M]` entering Protter III.39.  Its initial value is
the actual product `Z₀ M₀`; no zero-initial convention is imposed. -/
noncomputable def densityRawCovariation
    (hM : IsLocalMartingale M F P) (hF : F.IsUsual P) : ℝ≥0 → Ω → ℝ :=
  (isLocalMartingale_densityProcess (Q := Q) hF).isSemimartingale hF
    |>.quadraticCovariation (hM.isSemimartingale hF) hF

/-- The auxiliary integral `∫ [Z,M]₋ dW`, constructed in the source `P`
stochastic-integral environment after transporting the reverse density
semimartingale from `Q`. -/
noncomputable def girsanovMeyerAuxiliaryIntegral
    (hM : IsLocalMartingale M F P) (hPQ : P ≪ Q) (hF : F.IsUsual P) :
    ℝ≥0 → Ω → ℝ := by
  let hFQ : F.IsUsual Q := hF.of_absolutelyContinuous hPQ
  let hWQ : IsLocalMartingale (densityProcess P Q F) F Q :=
    isLocalMartingale_densityProcess hFQ
  let hWP : IsSemimartingale (densityProcess P Q F) F P :=
    (hWQ.isSemimartingale hFQ).absolutelyContinuous hPQ hFQ
  let hB : IsSemimartingale (densityRawCovariation (Q := Q) hM hF) F P :=
    ((isLocalMartingale_densityProcess (Q := Q) hF).isSemimartingale hF)
      |>.isSemimartingale_quadraticCovariation (hM.isSemimartingale hF) hF
  exact hWP.stochasticIntegral hF
    (hB.adapted.leftLimitProcess_of_usual hF hB.hasCadlagPaths)
    hB.hasCadlagPaths.hasCagladPaths_leftLimitProcess

/-- Division-free form of the right-value correction
`∫ (1 / Z_s) d[Z,M]_s`: reverse density times raw covariation, less the
auxiliary left integral from integration by parts. -/
noncomputable def girsanovMeyerCorrection
    (hM : IsLocalMartingale M F P) (hPQ : P ≪ Q) (hF : F.IsUsual P) :
    ℝ≥0 → Ω → ℝ :=
  densityProcess P Q F * densityRawCovariation (Q := Q) hM hF -
    girsanovMeyerAuxiliaryIntegral (Q := Q) hM hPQ hF

/-- Stochastic-integral expansion of the right-value correction:
`∫ W₋ d[Z,M] + [W,[Z,M]]`.  Integration by parts identifies this with
`girsanovMeyerCorrection`; the second bracket supplies the jump correction
turning the left-value stochastic integral into the source's right-value
Stieltjes integral. -/
noncomputable def girsanovMeyerRightIntegralCorrection
    (hM : IsLocalMartingale M F P) (hPQ : P ≪ Q) (hF : F.IsUsual P) :
    ℝ≥0 → Ω → ℝ := by
  let hFQ : F.IsUsual Q := hF.of_absolutelyContinuous hPQ
  let hWQ : IsLocalMartingale (densityProcess P Q F) F Q :=
    isLocalMartingale_densityProcess hFQ
  let hWP : IsSemimartingale (densityProcess P Q F) F P :=
    (hWQ.isSemimartingale hFQ).absolutelyContinuous hPQ hFQ
  let hB : IsSemimartingale (densityRawCovariation (Q := Q) hM hF) F P :=
    ((isLocalMartingale_densityProcess (Q := Q) hF).isSemimartingale hF)
      |>.isSemimartingale_quadraticCovariation (hM.isSemimartingale hF) hF
  exact hB.stochasticIntegral hF
      (hWP.adapted.leftLimitProcess_of_usual hF hWP.hasCadlagPaths)
      hWP.hasCadlagPaths.hasCagladPaths_leftLimitProcess +
    hWP.quadraticCovariation hB hF

/-- The division-free correction is indistinguishable from the explicit
right-value stochastic-integral expansion in the source environment. -/
theorem girsanovMeyerCorrection_indistinguishable_rightIntegral
    (hM : IsLocalMartingale M F P) (hPQ : P ≪ Q) (hF : F.IsUsual P) :
    Indistinguishable (girsanovMeyerCorrection (Q := Q) hM hPQ hF)
      (girsanovMeyerRightIntegralCorrection (Q := Q) hM hPQ hF) P := by
  let B := densityRawCovariation (Q := Q) hM hF
  let W := densityProcess P Q F
  let hFQ : F.IsUsual Q := hF.of_absolutelyContinuous hPQ
  let hWQ : IsLocalMartingale W F Q := isLocalMartingale_densityProcess hFQ
  let hWP : IsSemimartingale W F P :=
    (hWQ.isSemimartingale hFQ).absolutelyContinuous hPQ hFQ
  let hB : IsSemimartingale B F P :=
    ((isLocalMartingale_densityProcess (Q := Q) hF).isSemimartingale hF)
      |>.isSemimartingale_quadraticCovariation (hM.isSemimartingale hF) hF
  have hparts := hWP.integrationByParts hB hF
  filter_upwards [hparts] with ω hω t
  have hp := hω t
  change W t ω * B t ω -
      girsanovMeyerAuxiliaryIntegral (Q := Q) hM hPQ hF t ω =
    girsanovMeyerRightIntegralCorrection (Q := Q) hM hPQ hF t ω
  rw [girsanovMeyerAuxiliaryIntegral, girsanovMeyerRightIntegralCorrection]
  simp only [Pi.mul_apply, Pi.add_apply] at hp ⊢
  linarith

/-- The correction retains the raw bracket's actual initial product and hence
starts at `M₀` under equivalence.  Consequently the transformed local
martingale starts at zero without assuming `Z₀ = 1` or a trivial initial
sigma-algebra. -/
theorem girsanovMeyerCorrection_zero_ae
    (hM : IsLocalMartingale M F P) (hQP : Q ≪ P) (hPQ : P ≪ Q)
    (hF : F.IsUsual P) :
    girsanovMeyerCorrection (Q := Q) hM hPQ hF 0 =ᵐ[P] M 0 := by
  let B := densityRawCovariation (Q := Q) hM hF
  let W := densityProcess P Q F
  let Z := densityProcess Q P F
  let hFQ : F.IsUsual Q := hF.of_absolutelyContinuous hPQ
  let hWQ : IsLocalMartingale W F Q := isLocalMartingale_densityProcess hFQ
  let hWP : IsSemimartingale W F P :=
    (hWQ.isSemimartingale hFQ).absolutelyContinuous hPQ hFQ
  let hZP : IsSemimartingale Z F P :=
    (isLocalMartingale_densityProcess (Q := Q) hF).isSemimartingale hF
  let hMP : IsSemimartingale M F P := hM.isSemimartingale hF
  let hB : IsSemimartingale B F P :=
    hZP.isSemimartingale_quadraticCovariation hMP hF
  let H := leftLimitProcess B
  let haH : Adapted F H := hB.adapted.leftLimitProcess_of_usual hF hB.hasCadlagPaths
  let hrH : HasCagladPaths H P := hB.hasCadlagPaths.hasCagladPaths_leftLimitProcess
  have hN0 := hWP.stochasticIntegral_zero_ae hF haH hrH
  have hB0 := hZP.quadraticCovariation_zero_ae hMP hF
  have hWZ := densityProcess_reverse_mul_indistinguishable_one hQP hPQ hF
  filter_upwards [hN0, hB0, hWZ] with ω hN0 hB0 hWZ
  change W 0 ω * B 0 ω -
      girsanovMeyerAuxiliaryIntegral (Q := Q) hM hPQ hF 0 ω = M 0 ω
  rw [girsanovMeyerAuxiliaryIntegral]
  have hH0 : H 0 ω = 0 := by simp [H]
  have hB0' : B 0 ω = Z 0 ω * M 0 ω := by
    simpa only [B, Z, densityRawCovariation] using hB0
  rw [hN0, hH0, zero_mul, sub_zero, hB0']
  have hprod : W 0 ω * Z 0 ω = 1 := by
    simpa only [Pi.mul_apply] using hWZ 0
  rw [← mul_assoc, hprod, one_mul]

/-- On the common finite-variation/càdlàg event for the raw covariation, the
explicit correction is exactly the pathwise Stieltjes integral of the right
value `W_s` against `[Z,M]`. -/
theorem girsanovMeyerRightIntegralCorrection_eq_pathStieltjesIntegral_ae
    (hM : IsLocalMartingale M F P) (hPQ : P ≪ Q) (hF : F.IsUsual P) :
    let B := densityRawCovariation (Q := Q) hM hF
    let W := densityProcess P Q F
    ∀ᵐ ω ∂P, ∃ hv : LocallyBoundedVariationOn (B · ω) Set.univ,
      ∃ hr : IsCadlagPath (B · ω), ∀ t,
        girsanovMeyerRightIntegralCorrection (Q := Q) hM hPQ hF t ω =
          pathStieltjesIntegral (B · ω) hv hr.1 (W · ω) t := by
  intro B W
  let hFQ : F.IsUsual Q := hF.of_absolutelyContinuous hPQ
  let hWQ : IsLocalMartingale W F Q := isLocalMartingale_densityProcess hFQ
  let hWP : IsSemimartingale W F P :=
    (hWQ.isSemimartingale hFQ).absolutelyContinuous hPQ hFQ
  let hB : IsSemimartingale B F P :=
    ((isLocalMartingale_densityProcess (Q := Q) hF).isSemimartingale hF)
      |>.isSemimartingale_quadraticCovariation (hM.isSemimartingale hF) hF
  have hvB : HasFiniteVariationPaths B P :=
    ((isLocalMartingale_densityProcess (Q := Q) hF).isSemimartingale hF)
      |>.hasFiniteVariationPaths_quadraticCovariation (hM.isSemimartingale hF) hF
  filter_upwards [hWP.stochasticIntegral_leftLimit_add_quadraticCovariation_eq_pathStieltjesIntegral_ae
      hB hF hvB]
    with ω hω
  obtain ⟨hv, hr, he⟩ := hω
  refine ⟨hv, hr, fun t ↦ ?_⟩
  rw [girsanovMeyerRightIntegralCorrection]
  exact he t

/-- The auxiliary left integral is a local martingale under the target law.
The selected source-environment integral is identified with the target one by
absolute-continuity invariance of stochastic integration. -/
theorem isLocalMartingale_girsanovMeyerAuxiliaryIntegral
    (hM : IsLocalMartingale M F P) (hQP : Q ≪ P) (hPQ : P ≪ Q)
    (hF : F.IsUsual P) :
    IsLocalMartingale (girsanovMeyerAuxiliaryIntegral (Q := Q) hM hPQ hF) F Q := by
  let B := densityRawCovariation (Q := Q) hM hF
  let hFQ : F.IsUsual Q := hF.of_absolutelyContinuous hPQ
  let hWQ : IsLocalMartingale (densityProcess P Q F) F Q :=
    isLocalMartingale_densityProcess hFQ
  let hSWQ : IsSemimartingale (densityProcess P Q F) F Q := hWQ.isSemimartingale hFQ
  let hSWP : IsSemimartingale (densityProcess P Q F) F P :=
    hSWQ.absolutelyContinuous hPQ hFQ
  let hB : IsSemimartingale B F P :=
    ((isLocalMartingale_densityProcess (Q := Q) hF).isSemimartingale hF)
      |>.isSemimartingale_quadraticCovariation (hM.isSemimartingale hF) hF
  let H := leftLimitProcess B
  let haH : Adapted F H := hB.adapted.leftLimitProcess_of_usual hF hB.hasCadlagPaths
  let hrHP : HasCagladPaths H P := hB.hasCadlagPaths.hasCagladPaths_leftLimitProcess
  let hrHQ : HasCagladPaths H Q := hQP.ae_le hrHP
  have hNQ : IsLocalMartingale (hSWQ.stochasticIntegral hFQ haH hrHQ) F Q :=
    hSWQ.isLocalMartingale_stochasticIntegral hFQ hWQ haH hrHQ
  have heP : Indistinguishable
      (hSWP.stochasticIntegral hF haH (hPQ.ae_le hrHQ))
      (hSWQ.stochasticIntegral hFQ haH hrHQ) P :=
    hSWQ.stochasticIntegral_absolutelyContinuous hPQ hFQ hF haH hrHQ
  have heaux :
      girsanovMeyerAuxiliaryIntegral (Q := Q) hM hPQ hF =
        hSWP.stochasticIntegral hF haH (hPQ.ae_le hrHQ) := by
    rw [girsanovMeyerAuxiliaryIntegral]
  have heQ : Indistinguishable
      (girsanovMeyerAuxiliaryIntegral (Q := Q) hM hPQ hF)
      (hSWQ.stochasticIntegral hFQ haH hrHQ) Q := by
    filter_upwards [hQP.ae_le heP] with ω hω t
    rw [heaux]
    exact hω t
  exact hNQ.congr hFQ
    (hSWP.adapted_stochasticIntegral hF haH (hPQ.ae_le hrHQ)) heQ.symm

/-- Protter III.39, equivalent-measure Girsanov--Meyer theorem in a canonical
division-free form.  If `M` is a `P`-local martingale, subtracting the
right-value raw-covariation correction makes it a `Q`-local martingale. -/
theorem isLocalMartingale_sub_girsanovMeyerCorrection
    (hM : IsLocalMartingale M F P) (hQP : Q ≪ P) (hPQ : P ≪ Q)
    (hF : F.IsUsual P) :
    IsLocalMartingale (M - girsanovMeyerCorrection (Q := Q) hM hPQ hF) F Q := by
  let Z := densityProcess Q P F
  let W := densityProcess P Q F
  let B := densityRawCovariation (Q := Q) hM hF
  let N := girsanovMeyerAuxiliaryIntegral (Q := Q) hM hPQ hF
  let R := girsanovMeyerCorrection (Q := Q) hM hPQ hF
  let L := M - R
  let hFQ : F.IsUsual Q := hF.of_absolutelyContinuous hPQ
  let hZ : IsLocalMartingale Z F P := isLocalMartingale_densityProcess hF
  let hW : IsLocalMartingale W F Q := isLocalMartingale_densityProcess hFQ
  let hB : IsSemimartingale B F P :=
    (hZ.isSemimartingale hF).isSemimartingale_quadraticCovariation
      (hM.isSemimartingale hF) hF
  let hN : IsLocalMartingale N F Q :=
    isLocalMartingale_girsanovMeyerAuxiliaryIntegral hM hQP hPQ hF
  have haR : Adapted F R := (hW.1.mul hB.adapted).sub hN.1
  have haL : Adapted F L := hM.1.sub haR
  have hK : IsLocalMartingale (Z * M - B) F P := by
    simpa only [Z, B, densityRawCovariation] using
      hZ.isLocalMartingale_mul_sub_quadraticCovariation hM hF
  have hZN : IsLocalMartingale (Z * N) F P :=
    hN.mul_densityProcess_of_equivalent hQP hPQ hF
  have hsum : IsLocalMartingale ((Z * M - B) + Z * N) F P := hK.add hZN hF
  have hWZP : Indistinguishable (W * Z) (fun _ _ ↦ (1 : ℝ)) P :=
    densityProcess_reverse_mul_indistinguishable_one hQP hPQ hF
  have heZL : Indistinguishable (Z * L) ((Z * M - B) + Z * N) P := by
    filter_upwards [hWZP] with ω hω t
    have hZW : Z t ω * W t ω = 1 := by
      simpa only [Pi.mul_apply, mul_comm] using hω t
    change Z t ω * (M t ω - (W t ω * B t ω - N t ω)) =
      (Z t ω * M t ω - B t ω) + Z t ω * N t ω
    calc
      Z t ω * (M t ω - (W t ω * B t ω - N t ω)) =
          Z t ω * M t ω - (Z t ω * W t ω) * B t ω + Z t ω * N t ω := by ring
      _ = (Z t ω * M t ω - B t ω) + Z t ω * N t ω := by rw [hZW]; ring
  have hZL : IsLocalMartingale (Z * L) F P :=
    hsum.congr hF (hZ.1.mul haL) heZL.symm
  have hWZL : IsLocalMartingale (W * (Z * L)) F Q :=
    hZL.mul_densityProcess_of_equivalent hPQ hQP hFQ
  have heL : Indistinguishable (W * (Z * L)) L Q := by
    filter_upwards [hQP.ae_le hWZP] with ω hω t
    have hWZ : W t ω * Z t ω = 1 := by
      simpa only [Pi.mul_apply] using hω t
    change W t ω * (Z t ω * L t ω) = L t ω
    rw [← mul_assoc, hWZ, one_mul]
  exact hWZL.congr hFQ haL heL

/-- Protter III.39 in the explicit raw-covariation integral form.  The term
`[W,[Z,M]]` is part of the formula because the book integrates the right value
`W_s`, whereas the stochastic integral uses the predictable left value
`W_{s-}`. -/
theorem isLocalMartingale_sub_girsanovMeyerRightIntegralCorrection
    (hM : IsLocalMartingale M F P) (hQP : Q ≪ P) (hPQ : P ≪ Q)
    (hF : F.IsUsual P) :
    IsLocalMartingale
      (M - girsanovMeyerRightIntegralCorrection (Q := Q) hM hPQ hF) F Q := by
  let B := densityRawCovariation (Q := Q) hM hF
  let W := densityProcess P Q F
  let hFQ : F.IsUsual Q := hF.of_absolutelyContinuous hPQ
  let hWQ : IsLocalMartingale W F Q := isLocalMartingale_densityProcess hFQ
  let hWP : IsSemimartingale W F P :=
    (hWQ.isSemimartingale hFQ).absolutelyContinuous hPQ hFQ
  let hB : IsSemimartingale B F P :=
    ((isLocalMartingale_densityProcess (Q := Q) hF).isSemimartingale hF)
      |>.isSemimartingale_quadraticCovariation (hM.isSemimartingale hF) hF
  let haWl : Adapted F (leftLimitProcess W) :=
    hWP.adapted.leftLimitProcess_of_usual hF hWP.hasCadlagPaths
  let hrWl : HasCagladPaths (leftLimitProcess W) P :=
    hWP.hasCadlagPaths.hasCagladPaths_leftLimitProcess
  have haR : Adapted F
      (girsanovMeyerRightIntegralCorrection (Q := Q) hM hPQ hF) := by
    rw [girsanovMeyerRightIntegralCorrection]
    exact (hB.adapted_stochasticIntegral hF haWl hrWl).add
      (hWP.adapted_quadraticCovariation hB hF)
  have heR := girsanovMeyerCorrection_indistinguishable_rightIntegral
    (Q := Q) hM hPQ hF
  have he : Indistinguishable
      (M - girsanovMeyerCorrection (Q := Q) hM hPQ hF)
      (M - girsanovMeyerRightIntegralCorrection (Q := Q) hM hPQ hF) Q := by
    filter_upwards [hQP.ae_le heR] with ω hω t
    simp only [Pi.sub_apply, hω t]
  exact (isLocalMartingale_sub_girsanovMeyerCorrection hM hQP hPQ hF).congr
    hFQ (hM.1.sub haR) he

end ProbabilityTheory
