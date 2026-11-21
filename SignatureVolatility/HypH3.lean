module

public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.MeasureTheory.Function.L1Space.Integrable
public import SignatureVolatility.ExtTensorAlgebra.ExtTensorAlgebra


@[expose] public section

open MeasureTheory Set

namespace SignatureVolatility

/-- **Hypothesis H3** (paper): for every `λ > 0`,
`𝔼[exp(λ ∫₀ᵀ ξ_s² ds)] < ∞`, where `ξ` is the signature-volatility integrand.
This is the Novikov / exponential-integrability input to the square-integrable
stochastic-exponential construction (not the obsolete `ℓ ≠ 0` stub). -/
def HypH3 {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (T : ℝ) (ξ : ℝ → Ω → ℝ) : Prop :=
  ∀ lam : ℝ, 0 < lam →
    Integrable (fun ω => Real.exp (lam * ∫ s in (0 : ℝ)..T, (ξ s ω) ^ 2)) P

/-- Parameter-level remnant used by `SignatureVolatilityModel`: `ℓ` is nontrivial.
The analytic H3 above is imposed separately on `(P, T, ξ)` when building kits. -/
structure HypH3Param {d : ℕ} (hd : 0 < d) (ℓ : ExtTensorAlgebra (d + 1)) : Prop where
  nonZero : ℓ ≠ 0

end SignatureVolatility
