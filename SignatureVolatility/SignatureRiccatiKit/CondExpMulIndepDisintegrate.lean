module

public import SignatureVolatility.SignatureRiccatiKit.CounterexampleTensor
public import SignatureVolatility.SignatureRiccatiKit.CounterexampleV1
public import SignatureVolatility.ItoCalculusKit.OfMathFin
public import SignatureVolatility.DualPairing

/-!
# B5b. Conditional-expectation disintegration for an independent increment factor
-/

@[expose] public section

noncomputable section

open MeasureTheory Complex Filter Topology
open scoped ENNReal NNReal

namespace SignatureVolatility

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

/-- Standard `condExp` disintegration for `IndepFun`:
`P[g(X, Y) | m] = fun ω => ∫ y, g(X ω, y) ∂(P.map Y)` when `Y ⊥ m`
and `X` is `m`-measurable, specialised to the Doléans factorisation. -/
lemma condExp_mul_indep_disintegrate (M : SignatureVolatilityModel)
    (B : MultiBrownian Ω P M.d) {lam t : ℝ} (hlam : 1 ≤ lam)
    (ht : 0 ≤ t) (htT : t < M.T) :
    P[fun ω => Real.exp (dualPairing (counterexampleU0 M.hd lam)
        ((paperSetup B M.hT).W_hat M.T ω)) |
      (paperSetup B M.hT).signatureFiltration.σAlg t] =ᵐ[P]
      fun ω =>
        Real.exp (dualPairing (counterexampleU0 M.hd lam)
          ((paperSetup B M.hT).W_hat t ω)) *
        counterexampleV1 B M.hd (M.T - t)
          (lam ^ (1 / 3 : ℝ) * MultiBrownian.W B t ω ⟨0, M.hd⟩) := by
  sorry

end SignatureVolatility
