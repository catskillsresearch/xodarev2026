module

public import SignatureVolatility.SignatureRiccatiKit.BarrierU
public import SignatureVolatility.SignatureRiccatiKit.LintegralExpShifted
public import SignatureVolatility.ItoCalculusKit.BrownianQuadVarAS

/-!
# B4b. 1D Itô on `barrierU` plus the Doléans bound gives `v₁ x ≤ exp(u(0,x))`
-/

@[expose] public section

noncomputable section

open MeasureTheory Complex Filter Topology
open scoped ENNReal NNReal

namespace SignatureVolatility

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

/-- 1D Itô on the bounded `C^{1,2}` function `u(r, x + W_r)`, the PDE
inequality, and `lintegral_exp_ito_le_one`. -/
lemma integral_exp_shiftedExponent_le_exp_barrierU {d : ℕ}
    (B : MultiBrownian Ω P d) (hd : 0 < d)
    {s₀ β A x : ℝ} (hs₀ : 0 < s₀) (hβ : 0 < β)
    (hA2 : 2 ≤ A) (hAs : 2 * Real.sqrt (s₀ ^ 3) ≤ A)
    (hAβ : 2 * Real.sqrt β * s₀ ^ 3 ≤ A)
    (hx : 2 * A / s₀ ≤ x) :
    (∫ ω, Real.exp (counterexampleV1Exponent B hd s₀ x ω) ∂P) ≤
      Real.exp (barrierU s₀ β A 0 x) := by
  sorry

end SignatureVolatility
