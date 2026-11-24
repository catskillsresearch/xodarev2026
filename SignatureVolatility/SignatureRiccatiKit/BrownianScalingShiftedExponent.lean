module

public import SignatureVolatility.SignatureRiccatiKit.CounterexampleV1
public import SignatureVolatility.ItoCalculusKit.BrownianQuadVarAS

/-!
# B5a. Brownian scaling of the shifted exponent at factor `λ^{1/3}`
-/

@[expose] public section

noncomputable section

open MeasureTheory Complex Filter Topology
open scoped ENNReal NNReal

namespace SignatureVolatility

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

/-- Law uniqueness: `λ^{1/3} W'_{λ^{-2/3} ·}` has the same path law as `W`
on `[0, s₀]`, and the shifted exponent scales to `counterexampleV1AtHalf`. -/
lemma brownian_scaling_shiftedExponent (M : SignatureVolatilityModel)
    (B : MultiBrownian Ω P M.d) {lam : ℝ} (hlam : 1 ≤ lam)
    {t : ℝ} (ht : 0 ≤ t) (x : ℝ) :
    let s₀ := M.T / 2
    let c := lam ^ (-(2 / 3 : ℝ))
    (fun ω => Real.exp (counterexampleV1Exponent B M.hd (c * s₀)
        (lam ^ (1 / 3 : ℝ) * x) ω)) =ᵐ[P]
      fun ω =>
        Real.exp (counterexampleV1Exponent B M.hd s₀
          (lam ^ (1 / 3 : ℝ) * x) ω) := by
  sorry

end SignatureVolatility
