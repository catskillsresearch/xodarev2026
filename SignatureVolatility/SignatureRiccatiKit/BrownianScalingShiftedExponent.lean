module

public import SignatureVolatility.SignatureRiccatiKit.CounterexampleV1
public import SignatureVolatility.ItoCalculusKit.BrownianQuadVarAS
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
# B5a. Brownian scaling of the shifted exponent at factor `λ^{1/3}`
-/

@[expose] public section

noncomputable section

open MeasureTheory Complex Filter Topology
open scoped ENNReal NNReal

namespace SignatureVolatility

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

/-- The `λ`-scaled shifted Doléans exponent over `[0, s]` starting from `x`. -/
noncomputable def counterexampleV1ExponentScaled {d : ℕ} (B : MultiBrownian Ω P d)
    (hd : 0 < d) (lam s x : ℝ) (ω : Ω) : ℝ :=
  let w := fun r => MultiBrownian.W B r ω ⟨0, hd⟩
  (lam / 3) * ((x + w s) ^ 3 - x ^ 3)
    - lam * (∫ r in (0 : ℝ)..s, (x + w r))
    - (lam ^ 2 / 2) * (∫ r in (0 : ℝ)..s, (x + w r) ^ 4)

/-- Brownian scaling in **expectation** (not pathwise `=ᵐ[P]`), mapping the
`λ`-scaled exponent on `[0, s]` at `x` to the unscaled `counterexampleV1` at
time `λ^{2/3} s` and position `λ^{1/3} x`. The previous pathwise statement
comparing unscaled exponents at `c * s₀` and `s₀` is false for `λ > 1`. -/
lemma brownian_scaling_shiftedExponent {d : ℕ} (B : MultiBrownian Ω P d) (hd : 0 < d)
    {lam s : ℝ} (hlam : 0 < lam) (hs : 0 ≤ s) (x : ℝ) :
    ∫ ω, Real.exp (counterexampleV1ExponentScaled B hd lam s x ω) ∂P =
      counterexampleV1 B hd (lam ^ (2 / 3 : ℝ) * s) (lam ^ (1 / 3 : ℝ) * x) := by
  sorry

end SignatureVolatility
