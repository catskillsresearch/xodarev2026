/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.FiniteVariation.StieltjesExpectation
public import StochLean.Probability.Process.FiniteVariation.StieltjesKernelVariation
public import StochLean.Probability.Process.Measurability.PredictableKernelDuality
public import StochLean.Analysis.PathVariation.StieltjesContinuousCountable

/-! # Predictable duality for actual increasing processes

An integrable-variation increasing process and an increasing process with the
same martingale increments have equal expected Stieltjes integrals against
every nonnegative predictable function. This is proved from deterministic
rectangle increments, not from an assumed compensator or naturality theorem.
Only the first process needs integrable variation as an input.
-/

@[expose] public section

open MeasureTheory StochLean Set
open scoped NNReal ENNReal

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {F : Filtration ℝ≥0 mΩ}
  {P : Measure Ω} [IsFiniteMeasure P] {X Y : ℝ≥0 → Ω → ℝ}

/-- The integral uses the existing actual path-variation kernels. Initial
values are arbitrary and stay separate from these increment measures. -/
theorem lintegral_lintegral_totalVariationKernel_eq_of_martingale_sub
    (haX : Adapted F X) (hvX : ∀ ω, LocallyBoundedVariationOn (X · ω) univ)
    (hrX : ∀ ω, IsRightContinuousPath (X · ω)) (hmX : ∀ ω, Monotone (X · ω))
    (haY : Adapted F Y) (hvY : ∀ ω, LocallyBoundedVariationOn (Y · ω) univ)
    (hrY : ∀ ω, IsRightContinuousPath (Y · ω)) (hmY : ∀ ω, Monotone (Y · ω))
    (hiX : ∀ t, Integrable (X t) P) (hiY : ∀ t, Integrable (Y t) P)
    (hX : HasIntegrableVariation X P) (hM : Martingale (X - Y) F P)
    {H : ℝ≥0 × Ω → ℝ≥0∞} (hH : Measurable[F.predictable] H) :
    (∫⁻ ω, ∫⁻ t, H (t, ω) ∂totalVariationKernel X haX hvX hrX ω ∂P) =
      ∫⁻ ω, ∫⁻ t, H (t, ω) ∂totalVariationKernel Y haY hvY hrY ω ∂P := by
  let := isSFiniteKernel_totalVariationKernel haX hvX hrX
  let := isSFiniteKernel_totalVariationKernel haY hvY hrY
  apply Kernel.lintegral_lintegral_eq_of_predictable_rectangles F
    (hX.lintegral_totalVariationKernel_univ_lt_top haX hvX hrX) _ _ hH
  · intro E _
    have hzeroX (ω : Ω) : totalVariationKernel X haX hvX hrX ω {0} = 0 :=
      variationStieltjes_measure_zero _
    have hzeroY (ω : Ω) : totalVariationKernel Y haY hvY hrY ω {0} = 0 :=
      variationStieltjes_measure_zero _
    simp only [hzeroX, hzeroY]
  · intro s t E hE
    by_cases hst : s ≤ t
    · exact lintegral_totalVariationKernel_Ioc_eq_of_martingale_sub
        haX hvX hrX hmX haY hvY hrY hmY hiX hiY hM hst hE
    · simp only [Ioc_eq_empty_of_le (le_of_not_ge hst), measure_empty]

/-- A predictable set with countable time fibers is invisible to the actual
variation of an increasing process with a continuous martingale compensating
partner. The nullity is derived by integral duality, not assumed for `X`. -/
theorem ae_totalVariationKernel_eq_zero_of_predictable_countable
    (haX : Adapted F X) (hvX : ∀ ω, LocallyBoundedVariationOn (X · ω) univ)
    (hrX : ∀ ω, IsRightContinuousPath (X · ω)) (hmX : ∀ ω, Monotone (X · ω))
    (haY : Adapted F Y) (hvY : ∀ ω, LocallyBoundedVariationOn (Y · ω) univ)
    (hrY : ∀ ω, IsRightContinuousPath (Y · ω)) (hmY : ∀ ω, Monotone (Y · ω))
    (hcY : ∀ ω, Continuous (Y · ω))
    (hiX : ∀ t, Integrable (X t) P) (hiY : ∀ t, Integrable (Y t) P)
    (hX : HasIntegrableVariation X P) (hM : Martingale (X - Y) F P)
    {S : Set (ℝ≥0 × Ω)} (hS : MeasurableSet[F.predictable] S)
    (hcount : ∀ ω, {t | (t, ω) ∈ S}.Countable) :
    ∀ᵐ ω ∂P, totalVariationKernel X haX hvX hrX ω {t | (t, ω) ∈ S} = 0 := by
  classical
  let := isSFiniteKernel_totalVariationKernel haX hvX hrX
  have hSambient : MeasurableSet S := F.predictable_le_prod S hS
  have hm : Measurable (fun ω ↦ totalVariationKernel X haX hvX hrX ω
      {t | (t, ω) ∈ S}) := Kernel.measurable_kernel_prodMk_right hSambient
  apply (lintegral_eq_zero_iff hm).mp
  have he := lintegral_lintegral_totalVariationKernel_eq_of_martingale_sub
    haX hvX hrX hmX haY hvY hrY hmY hiX hiY hX hM
    (measurable_const.indicator hS : Measurable[F.predictable]
      (S.indicator (fun _ ↦ (1 : ℝ≥0∞))))
  have hfiber (ω : Ω) : MeasurableSet {t | (t, ω) ∈ S} :=
    measurable_prodMk_right hSambient
  have hstep (κ : Kernel Ω ℝ≥0) (ω : Ω) :
      (∫⁻ t, S.indicator (fun _ ↦ (1 : ℝ≥0∞)) (t, ω) ∂κ ω) =
        κ ω {t | (t, ω) ∈ S} := by
    change (∫⁻ t, {t | (t, ω) ∈ S}.indicator (fun _ ↦ (1 : ℝ≥0∞)) t ∂κ ω) = _
    rw [lintegral_indicator (hfiber ω)]
    simp
  simp_rw [hstep] at he
  rw [he]
  have hyzero (ω : Ω) : totalVariationKernel Y haY hvY hrY ω {t | (t, ω) ∈ S} = 0 :=
    totalVariationStieltjes_measure_countable_of_continuous (hvY ω) (hrY ω)
      (hcY ω) (hcount ω)
  simp only [hyzero, lintegral_zero]

end ProbabilityTheory
