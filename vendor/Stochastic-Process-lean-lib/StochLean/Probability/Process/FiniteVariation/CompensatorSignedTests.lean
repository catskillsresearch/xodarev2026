/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.FiniteVariation.CompensatorMonotoneVersion
public import StochLean.Probability.Process.FiniteVariation.SignedStieltjesDuality

/-! # Actual increasing compensators satisfy signed predictable tests

The compensator is constructed first, with everywhere-good increasing cadlag
paths. Actual signed Stieltjes duality then applies to its existing variation
kernel. The source is on the everywhere-good path representation required by
that kernel; it is not replaced by a different process.

The corrected signed test assumes finite expected absolute Stieltjes integral.
It proves integrability on both actual composition-product measures before
asserting equality of expected signed integrals. The integrals are increment
integrals without an atom at zero, so the arbitrary source initial value is
not silently included in or removed from them. No general predictable
stochastic-integral operator is constructed here.
-/

@[expose] public section

open MeasureTheory StochLean Filter Set
open scoped NNReal ENNReal

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
  {F : Filtration ℝ≥0 mΩ} {X : ℝ≥0 → Ω → ℝ}

/-- The actual unique predictable compensator, together with the corrected
signed-test identity for every predictable absolutely integrable Stieltjes
test. Every kernel is the existing path-variation kernel of its actual input. -/
theorem HasIntegrableVariation.exists_predictable_compensator_signed_tests
    (hvX : HasIntegrableVariation X P) (haX : Adapted F X) (hF : F.IsUsual P)
    (hcX : ∀ ω, IsCadlagPath (X · ω)) (hmX : ∀ ω, Monotone (X · ω))
    (hi0 : Integrable (X 0) P) :
    let κX := totalVariationKernel X haX
      (fun ω ↦ ((hmX ω).monotoneOn univ).locallyBoundedVariationOn) (fun ω ↦ (hcX ω).1)
    ∃ (A : ℝ≥0 → Ω → ℝ) (hpA : IsStronglyPredictable F A)
      (hpathA : ∀ ω, IsCadlagPath (A · ω) ∧ Monotone (A · ω)),
      A 0 = 0 ∧ HasIntegrableVariation A P ∧ IsUIMartingale (X - A) F P ∧
      (∀ H : ℝ≥0 × Ω → ℝ, Measurable[F.predictable] H →
        (∫⁻ ω, ∫⁻ t, ENNReal.ofReal ‖H (t, ω)‖ ∂κX ω ∂P) < ∞ →
        let κA := totalVariationKernel A hpA.stronglyAdapted.adapted
          (fun ω ↦ ((hpathA ω).2.monotoneOn univ).locallyBoundedVariationOn)
          (fun ω ↦ (hpathA ω).1.1)
        Integrable (fun p : Ω × ℝ≥0 ↦ H (p.2, p.1)) (P ⊗ₘ κX) ∧
          Integrable (fun p : Ω × ℝ≥0 ↦ H (p.2, p.1)) (P ⊗ₘ κA) ∧
          (∫ ω, ∫ t, H (t, ω) ∂κX ω ∂P) = ∫ ω, ∫ t, H (t, ω) ∂κA ω ∂P) ∧
      ∀ B : ℝ≥0 → Ω → ℝ,
        IsStronglyPredictable F B → HasFiniteVariationPaths B P →
        B 0 =ᵐ[P] 0 → IsLocalMartingale (X - B) F P → Indistinguishable A B P := by
  intro κX
  have hc : HasCadlagPaths X P := Eventually.of_forall hcX
  have hm : HasMonotonePaths X P := Eventually.of_forall hmX
  obtain ⟨A, hpA, hpathA, hA0, hvA, huA, hmean, huniq⟩ :=
    hvX.exists_unique_everywhere_monotone_predictable_compensator haX hF hc hi0 hm
  refine ⟨A, hpA, hpathA, hA0, hvA, huA, ?_, huniq⟩
  intro H hH habs
  exact integral_integral_totalVariationKernel_eq_of_martingale_sub haX
    (fun ω ↦ ((hmX ω).monotoneOn univ).locallyBoundedVariationOn)
    (fun ω ↦ (hcX ω).1) hmX hpA.stronglyAdapted.adapted
    (fun ω ↦ ((hpathA ω).2.monotoneOn univ).locallyBoundedVariationOn)
    (fun ω ↦ (hpathA ω).1.1) (fun ω ↦ (hpathA ω).2)
    (hvX.isClassD haX hF hc hi0).integrable (fun t ↦ (hmean t).1) hvX huA.1 hH habs

end ProbabilityTheory
