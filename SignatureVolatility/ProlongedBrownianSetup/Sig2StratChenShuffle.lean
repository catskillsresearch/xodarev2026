module

public import SignatureVolatility.ExtTensorAlgebra.Concat
public import SignatureVolatility.ExtTensorAlgebra.EvalShuffleBasis
public import SignatureVolatility.ProlongedBrownianSetup.Sig2Strat


@[expose] public section

open MeasureTheory

noncomputable section

namespace SignatureVolatility

/-!
# Chen and shuffle identities for `sig2Strat`

Paper Appendix: simplex decomposition ⇒ Chen; product-of-simplices ⇒ shuffle.

**Status: HOLE.** Requires the recursive Stratonovich integral construction (or geometric
rough-path limit of smooth signatures) before these identities can be discharged.
-/

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {d : ℕ}

/-- Chen identity: `sig2Strat 0 t = sig2Strat 0 s ⊗ₜ sig2Strat s t` on `0 ≤ s ≤ t ≤ T`. -/
lemma sig2Strat_chen (B : MultiBrownian Ω P d) {T : ℝ}
    ⦃s t : ℝ⦄ (_hs : 0 ≤ s) (_hst : s ≤ t) (_htT : t ≤ T) (ω : Ω) :
    sig2Strat B 0 t ω = sig2Strat B 0 s ω ⊗ₜ sig2Strat B s t ω := by
  -- Simplex split for Stratonovich iterated integrals (Chen 1977 / Friz–Victoir).
  sorry

/-- Shuffle identity on `sig2Strat 0 t`. -/
lemma sig2Strat_shuffle (B : MultiBrownian Ω P d) {T : ℝ}
    ⦃t : ℝ⦄ (_ht0 : 0 ≤ t) (_htT : t ≤ T) (I J : Word (d + 1)) (ω : Ω) :
    (sig2Strat B 0 t ω).coeff I * (sig2Strat B 0 t ω).coeff J =
      ExtTensorAlgebra.evalShuffleBasis I J (sig2Strat B 0 t ω) := by
  -- Product of simplices decomposes into shuffle-ordered simplices.
  sorry

end SignatureVolatility
