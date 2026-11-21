/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.Semimartingale.Classical
public import StochLean.Probability.Process.Semimartingale.MeasureChange.GirsanovMeyer
public import StochLean.Probability.Process.Semimartingale.StochasticIntegral.FiniteVariationPreservation

/-! # Classical semimartingales under equivalent measures

Classical semimartingales are invariant under an equivalent change of
probability measure.  The proof uses the Girsanov--Meyer correction for the
local-martingale part of a classical decomposition.  Its explicit right-value
form has locally finite variation and can therefore be absorbed into the
finite-variation part.

No Bichteler--Dellacherie converse is used here: the target-law classical
decomposition is constructed directly.
-/

@[expose] public section

open MeasureTheory Filter
open scoped NNReal

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}
  {P Q : Measure Ω} [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
  {F : Filtration ℝ≥0 mΩ} {M X : ℝ≥0 → Ω → ℝ}

/-- The explicit Girsanov--Meyer correction is adapted, càdlàg, and locally
of finite variation under the target law. -/
theorem girsanovMeyerRightIntegralCorrection_adapted_cadlag_finiteVariation
    (hM : IsLocalMartingale M F P) (hQP : Q ≪ P) (hPQ : P ≪ Q)
    (hF : F.IsUsual P) :
    let R := girsanovMeyerRightIntegralCorrection (Q := Q) hM hPQ hF
    Adapted F R ∧ HasCadlagPaths R Q ∧ HasFiniteVariationPaths R Q := by
  let B := densityRawCovariation (Q := Q) hM hF
  let W := densityProcess P Q F
  let hFQ : F.IsUsual Q := hF.of_absolutelyContinuous hPQ
  let hWQ : IsLocalMartingale W F Q := isLocalMartingale_densityProcess hFQ
  let hWP : IsSemimartingale W F P :=
    (hWQ.isSemimartingale hFQ).absolutelyContinuous hPQ hFQ
  let hB : IsSemimartingale B F P :=
    ((isLocalMartingale_densityProcess (Q := Q) hF).isSemimartingale hF)
      |>.isSemimartingale_quadraticCovariation (hM.isSemimartingale hF) hF
  let Wl := leftLimitProcess W
  let haWl : Adapted F Wl :=
    hWP.adapted.leftLimitProcess_of_usual hF hWP.hasCadlagPaths
  let hrWl : HasCagladPaths Wl P :=
    hWP.hasCadlagPaths.hasCagladPaths_leftLimitProcess
  let J := hB.stochasticIntegral hF haWl hrWl
  let C := hWP.quadraticCovariation hB hF
  have hvB : HasFiniteVariationPaths B P :=
    ((isLocalMartingale_densityProcess (Q := Q) hF).isSemimartingale hF)
      |>.hasFiniteVariationPaths_quadraticCovariation (hM.isSemimartingale hF) hF
  have haJ : Adapted F J := hB.adapted_stochasticIntegral hF haWl hrWl
  have hcJ : HasCadlagPaths J P := hB.hasCadlagPaths_stochasticIntegral hF haWl hrWl
  have hvJ : HasFiniteVariationPaths J P :=
    hB.hasFiniteVariationPaths_stochasticIntegral hF hvB haWl hrWl
  have haC : Adapted F C := hWP.adapted_quadraticCovariation hB hF
  have hcC : HasCadlagPaths C P := hWP.hasCadlagPaths_quadraticCovariation hB hF
  have hvC : HasFiniteVariationPaths C P :=
    hWP.hasFiniteVariationPaths_quadraticCovariation hB hF
  have hdef : girsanovMeyerRightIntegralCorrection (Q := Q) hM hPQ hF = J + C := by
    rw [girsanovMeyerRightIntegralCorrection]
  refine ⟨hdef ▸ haJ.add haC, hQP.ae_le (hdef ▸ hcJ.add hcC), ?_⟩
  rw [hdef]
  filter_upwards [hQP.ae_le hvJ, hQP.ae_le hvC] with ω hJω hCω
  exact StochLean.locallyBoundedVariationOn_add hJω hCω

/-- Classical semimartingales remain classical semimartingales after an
equivalent change of probability measure. -/
theorem IsClassicalSemimartingale.equivalentMeasure
    (hX : IsClassicalSemimartingale X F P) (hQP : Q ≪ P) (hPQ : P ≪ Q)
    (hF : F.IsUsual P) : IsClassicalSemimartingale X F Q := by
  obtain ⟨haX, hcX, M, A, hM, haA, hcA, hvA, hM0, hA0, heX⟩ := hX
  let R := girsanovMeyerRightIntegralCorrection (Q := Q) hM hPQ hF
  let N := M - R
  let C := A + R
  have hN : IsLocalMartingale N F Q := by
    simpa only [N, R] using
      isLocalMartingale_sub_girsanovMeyerRightIntegralCorrection hM hQP hPQ hF
  obtain ⟨haR, hcR, hvR⟩ :=
    girsanovMeyerRightIntegralCorrection_adapted_cadlag_finiteVariation
      hM hQP hPQ hF
  have hR0P : R 0 =ᵐ[P] M 0 := by
    exact (girsanovMeyerCorrection_indistinguishable_rightIntegral
      (Q := Q) hM hPQ hF).ae_eq 0 |>.symm.trans
        (girsanovMeyerCorrection_zero_ae hM hQP hPQ hF)
  have hN0 : N 0 =ᵐ[Q] 0 := by
    filter_upwards [hQP.ae_le hM0, hQP.ae_le hR0P] with ω hM0ω hR0ω
    change M 0 ω - R 0 ω = 0
    rw [hR0ω, sub_self]
  have hC0 : C 0 =ᵐ[Q] 0 := by
    filter_upwards [hQP.ae_le hA0, hQP.ae_le hM0, hQP.ae_le hR0P]
      with ω hA0ω hM0ω hR0ω
    change A 0 ω + R 0 ω = 0
    simp only [Pi.zero_apply] at hA0ω hM0ω
    rw [hR0ω, hM0ω, hA0ω, add_zero]
  have hvC : HasFiniteVariationPaths C Q := by
    filter_upwards [hQP.ae_le hvA, hvR] with ω hAω hRω
    exact StochLean.locallyBoundedVariationOn_add hAω hRω
  have he : Indistinguishable X ((fun _ ↦ X 0) + N + C) Q := by
    filter_upwards [hQP.ae_le heX] with ω hω t
    change X t ω = X 0 ω + (M t ω - R t ω) + (A t ω + R t ω)
    calc
      X t ω = X 0 ω + M t ω + A t ω := by
        simpa only [Pi.add_apply] using hω t
      _ = X 0 ω + (M t ω - R t ω) + (A t ω + R t ω) := by ring
  have hcAQ : HasCadlagPaths A Q := hQP.ae_le hcA
  exact ⟨haX, hQP.ae_le hcX, N, C, hN, haA.add haR,
    hcAQ.add hcR, hvC, hN0, hC0, he⟩

/-- Under mutually absolutely continuous probability laws, the classical
semimartingale predicate is unchanged. -/
theorem isClassicalSemimartingale_iff_of_mutuallyAbsolutelyContinuous
    (hQP : Q ≪ P) (hPQ : P ≪ Q) (hF : F.IsUsual P) :
    IsClassicalSemimartingale X F P ↔ IsClassicalSemimartingale X F Q := by
  constructor
  · exact fun hX ↦ hX.equivalentMeasure hQP hPQ hF
  · exact fun hX ↦ hX.equivalentMeasure hPQ hQP (hF.of_absolutelyContinuous hPQ)

end ProbabilityTheory
