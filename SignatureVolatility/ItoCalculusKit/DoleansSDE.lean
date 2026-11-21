module

public import SignatureVolatility.ItoCalculusKit.MathFinBridge


@[expose] public section

open MeasureTheory Set

noncomputable section

namespace SignatureVolatility

/-!
# Doléans SDE for the MathFin-bridge Itô kit

The pathwise / a.e. identity
`s₀ · ℰ(σ)_t = s₀ + ∫₀ᵗ s₀ · ℰ(σ)_s · σ_s dW`
for the dyadic limUnder totalization, under `IntegrableOn σ²`. Discharged by the Föllmer–Itô
formula along continuous BM paths (MathFin `discountedGBM_eq_itoIntegral` /
`DoleansStepRepresentation` + L² density of steps).
-/

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {d : ℕ}

/-- Doléans SDE under pathwise square-integrability of `σ`. -/
axiom kit_doleans_sde {T : ℝ} (B : MultiBrownian Ω P d) (hT : 0 < T)
    (s₀ : ℝ) (σ : ℝ → Ω → ℝ)
    (hquad : ∀ᵐ ω ∂P, IntegrableOn (fun s => (σ s ω) ^ 2) (Icc 0 T) volume) :
    ∀ t ∈ Icc 0 T, ∀ᵐ ω ∂P,
      s₀ * kitDoleansExp B σ t ω =
        s₀ + kitItoInt B (fun s ω' => (s₀ * kitDoleansExp B σ s ω') * σ s ω') t ω

end SignatureVolatility
