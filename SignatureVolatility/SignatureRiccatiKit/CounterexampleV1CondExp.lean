module

public import SignatureVolatility.SignatureRiccatiKit.CounterexampleTensor
public import SignatureVolatility.SignatureRiccatiKit.CounterexampleV1
public import SignatureVolatility.SignatureRiccatiKit.BrownianScalingShiftedExponent
public import SignatureVolatility.SignatureRiccatiKit.CondExpMulIndepDisintegrate
public import SignatureVolatility.ItoCalculusKit.OfMathFin
public import SignatureVolatility.DualPairing


/-!
# B5. Conditional-expectation factorisation

For every `λ ≥ 1`, at `t = T - λ^{-2/3}(T/2)`,
`𝔼[M_T^(λ) | ℱ_t] = M_t^(λ) * v₁(λ^{1/3} W_t)` a.s.
-/

@[expose] public section

noncomputable section

open MeasureTheory

namespace SignatureVolatility

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

/-- **B5.** Conditional-expectation factorisation of the Doléans exponential
against `v₁`. -/
lemma counterexampleV1_condExp (M : SignatureVolatilityModel)
    (B : MultiBrownian Ω P M.d) :
    ∀ lam : ℝ, 1 ≤ lam →
      let s_lam := lam ^ (-(2 / 3 : ℝ)) * (M.T / 2)
      let t_lam := M.T - s_lam
      P[fun ω => Real.exp (dualPairing (counterexampleU0 M.hd lam)
          ((paperSetup B M.hT).W_hat M.T ω)) |
        (paperSetup B M.hT).signatureFiltration.σAlg t_lam] =ᵐ[P]
        fun ω =>
          Real.exp (dualPairing (counterexampleU0 M.hd lam)
            ((paperSetup B M.hT).W_hat t_lam ω)) *
          counterexampleV1AtHalf M B
            (lam ^ (1 / 3 : ℝ) * MultiBrownian.W B t_lam ω ⟨0, M.hd⟩) := by
  sorry

end SignatureVolatility
