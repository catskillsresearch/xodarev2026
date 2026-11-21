/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.FiniteVariation.CompensatorSignedTests
public import StochLean.Probability.Process.FiniteVariation.CanonicalCompensator
public import StochLean.Probability.Process.FiniteVariation.MonotoneCadlagVersion
public import StochLean.Probability.Process.FiniteVariation.StieltjesCongr

/-! # Signed compensator tests for common-AE monotone cadlag sources

The source's genuine everywhere-good version is constructed by an initial
null-set reset. Existing signed kernel duality applies on that legal path
domain, and its predictable compensator is identified with the sole actual
canonical compensator of the original source. The original source itself
minus this predictable version is UI.

The absolute-integrability hypothesis concerns the actual source-version
Stieltjes kernel. Common-path equality preserves whole kernel fibers, so
it is independent of which legitimate everywhere-good version is used.
Kernels have no atom at zero: this statement concerns increment integrals,
not an uncentered Chapter II integral with an unchecked initial product.
-/

@[expose] public section

open MeasureTheory StochLean Filter Set
open scoped NNReal ENNReal

namespace ProbabilityTheory.HasIntegrableVariation

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
  {F : Filtration ℝ≥0 mΩ} {X : ℝ≥0 → Ω → ℝ}

/-- The corrected signed-test consumer accepts the original AE-cadlag,
AE-monotone source. Both required everywhere-good kernel representatives
are constructed, and compensation is coherent with the actual selector. -/
theorem exists_predictable_compensator_signed_tests_of_ae
    (hvX : HasIntegrableVariation X P) (haX : Adapted F X) (hF : F.IsUsual P)
    (hcX : HasCadlagPaths X P) (hmX : HasMonotonePaths X P)
    (hi0 : Integrable (X 0) P) :
    ∃ (Y : ℝ≥0 → Ω → ℝ) (haY : Adapted F Y)
      (hpathY : ∀ ω, IsCadlagPath (Y · ω) ∧ Monotone (Y · ω)),
      Indistinguishable X Y P ∧
      ∃ (A : ℝ≥0 → Ω → ℝ) (hpA : IsStronglyPredictable F A)
        (hpathA : ∀ ω, IsCadlagPath (A · ω) ∧ Monotone (A · ω)),
        Indistinguishable
          (hvX.hasLocallyIntegrableVariation.predictableCompensator haX hF hcX) A P ∧
        A 0 = 0 ∧ HasIntegrableVariation A P ∧ IsUIMartingale (X - A) F P ∧
        ∀ H : ℝ≥0 × Ω → ℝ, Measurable[F.predictable] H →
          let κY := totalVariationKernel Y haY
            (fun ω ↦ ((hpathY ω).2.monotoneOn univ).locallyBoundedVariationOn)
            (fun ω ↦ (hpathY ω).1.1)
          let κA := totalVariationKernel A hpA.stronglyAdapted.adapted
            (fun ω ↦ ((hpathA ω).2.monotoneOn univ).locallyBoundedVariationOn)
            (fun ω ↦ (hpathA ω).1.1)
          (∫⁻ ω, ∫⁻ t, ENNReal.ofReal ‖H (t, ω)‖ ∂κY ω ∂P) < ∞ →
            Integrable (fun p : Ω × ℝ≥0 ↦ H (p.2, p.1)) (P ⊗ₘ κY) ∧
              Integrable (fun p : Ω × ℝ≥0 ↦ H (p.2, p.1)) (P ⊗ₘ κA) ∧
              (∫ ω, ∫ t, H (t, ω) ∂κY ω ∂P) = ∫ ω, ∫ t, H (t, ω) ∂κA ω ∂P := by
  obtain ⟨Y, haY, hpathY, heXY⟩ :=
    haX.exists_cadlag_monotone_indistinguishable_of_usual hF hcX hmX
  have hvY : HasIntegrableVariation Y P := hvX.congr heXY
  have hiY : Integrable (Y 0) P := hi0.congr (heXY.ae_eq 0)
  obtain ⟨A, hpA, hpathA, hA0, hvA, huYA, htest, _⟩ :=
    hvY.exists_predictable_compensator_signed_tests haY hF
      (fun ω ↦ (hpathY ω).1) (fun ω ↦ (hpathY ω).2) hiY
  have heXA : Indistinguishable (Y - A) (X - A) P := by
    filter_upwards [heXY] with ω hω t
    change Y t ω - A t ω = X t ω - A t ω
    rw [hω t]
  have huXA : IsUIMartingale (X - A) F P :=
    huYA.congr (haX.sub hpA.stronglyAdapted.adapted) heXA
  have hcA : HasCadlagPaths A P := Eventually.of_forall fun ω ↦ (hpathA ω).1
  have heA := hvX.hasLocallyIntegrableVariation.predictableCompensator_unique
    haX hF hcX hpA hvA.hasFiniteVariationPaths
    (Eventually.of_forall fun ω ↦ congrFun hA0 ω)
    (huXA.isLocalMartingale (hcX.sub hcA))
  refine ⟨Y, haY, hpathY, heXY, A, hpA, hpathA, heA, hA0, hvA, huXA, ?_⟩
  intro H hH
  exact htest H hH

end ProbabilityTheory.HasIntegrableVariation
