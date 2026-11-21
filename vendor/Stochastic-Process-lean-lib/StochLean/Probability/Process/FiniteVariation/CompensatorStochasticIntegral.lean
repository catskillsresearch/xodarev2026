/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.FiniteVariation.CompensatorMonotoneVersion
public import StochLean.Probability.Process.FiniteVariation.SignedStieltjesDuality
public import StochLean.Probability.Process.Semimartingale.StochasticIntegral.FiniteVariation
public import StochLean.Analysis.PathVariation.MonotoneIntegralMeasure

/-! # Signed compensator tests for the actual Chapter II integral

An adapted, common-AE caglad integrand has a genuinely predictable version.
Its predictable restriction to `(0,T]` is an admissible signed kernel test.
The existing FV agreement identifies both actual Chapter II integrals with
these Stieltjes integrals after subtracting their original initial products.

The finite expected absolute Stieltjes integral proves integrability of these
centered values, not of unchecked initial products. The integrators are on
the everywhere-cadlag increasing representation required by their existing
kernels; the original integrand need only be caglad almost surely. No new
stochastic-integral operator or extension to arbitrary predictable integrands
is introduced.
-/

@[expose] public section

open MeasureTheory StochLean Filter Set
open scoped NNReal ENNReal

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
  {F : Filtration ℝ≥0 mΩ} {X Y H G : ℝ≥0 → Ω → ℝ}

section Finite

variable [IsFiniteMeasure P]

private theorem integrable_integral_of_integrable_compProd
    (κ : Kernel Ω ℝ≥0) [IsSFiniteKernel κ] {f : Ω × ℝ≥0 → ℝ}
    (hm : Measurable f) (hi : Integrable f (P ⊗ₘ κ)) :
    Integrable (fun ω ↦ ∫ t, f (ω, t) ∂κ ω) P := by
  have hn := ((Measure.integrable_compProd_iff hi.aestronglyMeasurable).mp hi).2
  exact hn.mono' hm.stronglyMeasurable.integral_kernel_prod_right'.aestronglyMeasurable
    (Eventually.of_forall fun ω ↦ norm_integral_le_integral_norm _)

private theorem stochasticIntegral_sub_initial_ae_eq_integral_cutoff
    (hX : IsSemimartingale X F P) (hF : F.IsUsual P)
    (hcX : ∀ ω, IsCadlagPath (X · ω)) (hmX : ∀ ω, Monotone (X · ω))
    (haH : Adapted F H) (hrH : HasCagladPaths H P)
    (hHG : Indistinguishable H G P) (T : ℝ≥0) :
    (fun ω ↦ hX.stochasticIntegral hF haH hrH T ω - H 0 ω * X 0 ω) =ᵐ[P]
      fun ω ↦ ∫ t, ((Ioc 0 T) ×ˢ (univ : Set Ω)).indicator
        (Function.uncurry G) (t, ω)
        ∂totalVariationKernel X hX.adapted
          (fun ω ↦ ((hmX ω).monotoneOn univ).locallyBoundedVariationOn)
          (fun ω ↦ (hcX ω).1) ω := by
  have he := hX.stochasticIntegral_eq_finiteVariationIntegral hF
    (fun ω ↦ ((hmX ω).monotoneOn univ).locallyBoundedVariationOn)
    (fun ω ↦ (hcX ω).1) haH hrH
  filter_upwards [he, hHG] with ω heω hHGω
  let V : StieltjesFunction ℝ≥0 := ⟨(X · ω), hmX ω, (hcX ω).1⟩
  have hmeasure : totalVariationKernel X hX.adapted
      (fun ω ↦ ((hmX ω).monotoneOn univ).locallyBoundedVariationOn)
      (fun ω ↦ (hcX ω).1) ω = V.measure :=
    totalVariationStieltjes_measure_of_stieltjes V
      (((hmX ω).monotoneOn univ).locallyBoundedVariationOn)
  rw [heω T]
  change pathStieltjesIntegral (X · ω) _ _ (H · ω) T - H 0 ω * X 0 ω = _
  rw [hmeasure]
  have hpath := pathStieltjesIntegral_eq_stieltjesIntegral V
    (((hmX ω).monotoneOn univ).locallyBoundedVariationOn) (H · ω) T
  change pathStieltjesIntegral (X · ω) _ _ (H · ω) T =
    H 0 ω * X 0 ω + ∫ t in Ioc 0 T, H t ω ∂V.measure at hpath
  rw [hpath, add_sub_cancel_left]
  rw [← integral_indicator measurableSet_Ioc]
  apply integral_congr_ae
  exact Eventually.of_forall fun t ↦ by
    by_cases ht : t ∈ Ioc 0 T <;> simp [ht, Function.uncurry, hHGω t]

/-- Actual signed duality for finite-time Chapter II integrals. Only the
centered values are asserted integrable: the original initial products are
not controlled by an increment-kernel absolute-integrability hypothesis. -/
theorem integrable_and_integral_stochasticIntegral_sub_initial_eq_of_martingale_sub
    (haX : Adapted F X) (hcX : ∀ ω, IsCadlagPath (X · ω))
    (hmX : ∀ ω, Monotone (X · ω))
    (haY : Adapted F Y) (hcY : ∀ ω, IsCadlagPath (Y · ω))
    (hmY : ∀ ω, Monotone (Y · ω))
    (hiX : ∀ t, Integrable (X t) P) (hiY : ∀ t, Integrable (Y t) P)
    (hvX : HasIntegrableVariation X P) (hM : Martingale (X - Y) F P)
    (hF : F.IsUsual P) (haH : Adapted F H) (hrH : HasCagladPaths H P) (T : ℝ≥0)
    (habs : (∫⁻ ω, ∫⁻ t in Ioc 0 T, ENNReal.ofReal ‖H t ω‖
      ∂totalVariationKernel X haX
        (fun ω ↦ ((hmX ω).monotoneOn univ).locallyBoundedVariationOn)
        (fun ω ↦ (hcX ω).1) ω ∂P) < ∞) :
    let hSX := hvX.hasFiniteVariationPaths.isSemimartingale haX hF
      (Eventually.of_forall hcX)
    let hSY := (show HasFiniteVariationPaths Y P from Eventually.of_forall
      (fun ω ↦ ((hmY ω).monotoneOn univ).locallyBoundedVariationOn)).isSemimartingale
      haY hF (Eventually.of_forall hcY)
    Integrable (fun ω ↦ hSX.stochasticIntegral hF haH hrH T ω - H 0 ω * X 0 ω) P ∧
      Integrable (fun ω ↦ hSY.stochasticIntegral hF haH hrH T ω - H 0 ω * Y 0 ω) P ∧
      (∫ ω, hSX.stochasticIntegral hF haH hrH T ω - H 0 ω * X 0 ω ∂P) =
        ∫ ω, hSY.stochasticIntegral hF haH hrH T ω - H 0 ω * Y 0 ω ∂P := by
  intro hSX hSY
  classical
  let κX := totalVariationKernel X haX
    (fun ω ↦ ((hmX ω).monotoneOn univ).locallyBoundedVariationOn) (fun ω ↦ (hcX ω).1)
  let κY := totalVariationKernel Y haY
    (fun ω ↦ ((hmY ω).monotoneOn univ).locallyBoundedVariationOn) (fun ω ↦ (hcY ω).1)
  let : IsSFiniteKernel κX := isSFiniteKernel_totalVariationKernel haX _ _
  let : IsSFiniteKernel κY := isSFiniteKernel_totalVariationKernel haY _ _
  obtain ⟨G, hHG, hpG, _⟩ :=
    haH.exists_predictable_indistinguishable_of_hasLeftContinuousPaths hF
      hrH.hasLeftContinuousPaths
  let K : ℝ≥0 × Ω → ℝ := ((Ioc 0 T) ×ˢ (univ : Set Ω)).indicator (Function.uncurry G)
  have hmK : Measurable[F.predictable] K :=
    hpG.measurable.indicator (measurableSet_predictable_Ioc_prod 0 T MeasurableSet.univ)
  have heAbs : (∫⁻ ω, ∫⁻ t, ENNReal.ofReal ‖K (t, ω)‖ ∂κX ω ∂P) =
      ∫⁻ ω, ∫⁻ t in Ioc 0 T, ENNReal.ofReal ‖H t ω‖ ∂κX ω ∂P := by
    apply lintegral_congr_ae
    filter_upwards [hHG] with ω hω
    rw [← lintegral_indicator measurableSet_Ioc]
    apply lintegral_congr_ae
    exact Eventually.of_forall fun t ↦ by
      by_cases ht : t ∈ Ioc 0 T <;> simp [K, ht, Function.uncurry, hω t]
  have habsK : (∫⁻ ω, ∫⁻ t, ENNReal.ofReal ‖K (t, ω)‖ ∂κX ω ∂P) < ∞ := by
    rw [heAbs]
    exact habs
  obtain ⟨hiKX, hiKY, heK⟩ := integral_integral_totalVariationKernel_eq_of_martingale_sub
    haX (fun ω ↦ ((hmX ω).monotoneOn univ).locallyBoundedVariationOn)
    (fun ω ↦ (hcX ω).1) hmX haY
    (fun ω ↦ ((hmY ω).monotoneOn univ).locallyBoundedVariationOn)
    (fun ω ↦ (hcY ω).1) hmY hiX hiY hvX hM hmK habsK
  have hmf : Measurable (fun p : Ω × ℝ≥0 ↦ K (p.2, p.1)) :=
    (hmK.mono F.predictable_le_prod le_rfl).comp measurable_swap
  have hiIX := integrable_integral_of_integrable_compProd κX hmf hiKX
  have hiIY := integrable_integral_of_integrable_compProd κY hmf hiKY
  have heX := stochasticIntegral_sub_initial_ae_eq_integral_cutoff hSX hF hcX hmX haH hrH hHG T
  have heY := stochasticIntegral_sub_initial_ae_eq_integral_cutoff hSY hF hcY hmY haH hrH hHG T
  exact ⟨hiIX.congr heX.symm, hiIY.congr heY.symm,
    (integral_congr_ae heX).trans (heK.trans (integral_congr_ae heY.symm))⟩

end Finite

variable [IsProbabilityMeasure P]

/-- Construct an actual predictable compensator and identify its finite-time
Chapter II signed tests for every adapted AE-caglad integrand on the genuine
expected-absolute-integral domain. Initial products remain explicitly centered. -/
theorem HasIntegrableVariation.exists_predictable_compensator_stochasticIntegral_tests
    (hvX : HasIntegrableVariation X P) (haX : Adapted F X) (hF : F.IsUsual P)
    (hcX : ∀ ω, IsCadlagPath (X · ω)) (hmX : ∀ ω, Monotone (X · ω))
    (hi0 : Integrable (X 0) P) :
    ∃ (A : ℝ≥0 → Ω → ℝ) (hpA : IsStronglyPredictable F A)
      (hpathA : ∀ ω, IsCadlagPath (A · ω) ∧ Monotone (A · ω)),
      A 0 = 0 ∧ ∃ hvA : HasIntegrableVariation A P, IsUIMartingale (X - A) F P ∧
      ∀ (H : ℝ≥0 → Ω → ℝ) (haH : Adapted F H) (hrH : HasCagladPaths H P) (T : ℝ≥0),
        (∫⁻ ω, ∫⁻ t in Ioc 0 T, ENNReal.ofReal ‖H t ω‖
          ∂totalVariationKernel X haX
            (fun ω ↦ ((hmX ω).monotoneOn univ).locallyBoundedVariationOn)
            (fun ω ↦ (hcX ω).1) ω ∂P) < ∞ →
        let hSX := hvX.hasFiniteVariationPaths.isSemimartingale haX hF
          (Eventually.of_forall hcX)
        let hSA := hvA.hasFiniteVariationPaths.isSemimartingale hpA.stronglyAdapted.adapted hF
          (Eventually.of_forall fun ω ↦ (hpathA ω).1)
        Integrable (fun ω ↦ hSX.stochasticIntegral hF haH hrH T ω - H 0 ω * X 0 ω) P ∧
          Integrable (fun ω ↦ hSA.stochasticIntegral hF haH hrH T ω - H 0 ω * A 0 ω) P ∧
          (∫ ω, hSX.stochasticIntegral hF haH hrH T ω - H 0 ω * X 0 ω ∂P) =
            ∫ ω, hSA.stochasticIntegral hF haH hrH T ω - H 0 ω * A 0 ω ∂P := by
  have hc : HasCadlagPaths X P := Eventually.of_forall hcX
  obtain ⟨A, hpA, hpathA, hA0, hvA, huA, hmean, _⟩ :=
    hvX.exists_unique_everywhere_monotone_predictable_compensator haX hF hc hi0
      (Eventually.of_forall hmX)
  refine ⟨A, hpA, hpathA, hA0, hvA, huA, ?_⟩
  intro H haH hrH T habs
  exact integrable_and_integral_stochasticIntegral_sub_initial_eq_of_martingale_sub
    haX hcX hmX hpA.stronglyAdapted.adapted
    (fun ω ↦ (hpathA ω).1) (fun ω ↦ (hpathA ω).2)
    (hvX.integrable haX hF hc hi0) (fun t ↦ (hmean t).1) hvX huA.1 hF haH hrH T habs

end ProbabilityTheory
