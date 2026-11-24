module

public import SignatureVolatility.Prop58BlackScholesDepthFalse

@[expose] public section

open MeasureTheory

namespace SignatureVolatility

/-!
# Theorem C (paper Theorem 56 / PDF Theorem 5.3): price-filtration completeness depth

**The paper's claim.** The market of `S` plus finitely many calls is complete on `ℱ^S_T` iff
`N^*_S < ∞`. Here `N^*_S` is the least `N` for which
`closure span{⟨e_I, Ŵ_T⟩ : |I| ≤ N} ∩ L²(ℱ^S_T)` is (dense in) `L²(ℱ^S_T)` (Definition 55).

**What is true.** That space lies in the span of finitely many vectors, so it is
finite-dimensional and closed. Hence the right-hand side "`N^*_S < ∞`" holds only when
`L²(ℱ^S_T)` is finite-dimensional. In every non-degenerate model, `N^*_S = ∞` and no finite
depth is dense (`theorem_C_depth_infinite`). This includes Black–Scholes
(`theorem_C_blackScholes_depth_infinite`), so the paper's Proposition 58 value `N^*_S = 0` is
false (`not_prop58_blackScholes_depth_zero`).

Theorem C would therefore say that every non-degenerate market with finitely many calls is
incomplete on `ℱ^S_T`. That contradicts the classical completeness of Black–Scholes (Brownian
martingale representation on `ℱ^S = ℱ^W`). The martingale representation theorem is not
formalised in this repository, so the left-hand side of the "iff" is not refuted in Lean. The
paper's equivalence cannot hold as stated, and only its right-hand side is settled formally.
-/

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

/-- **Theorem C, right-hand side, in every non-degenerate market.** If `L²(ℱ^S_T, ℚ)` is
infinite-dimensional, then the Definition 55 depth is `∞`, and no finite-depth closed signature
span restricted to the price filtration is dense in `L²(ℱ^S_T, ℚ)`. -/
theorem theorem_C_depth_infinite (mkt : MarketData Ω P)
    (hinf : ¬ FiniteDimensional ℝ mkt.L2S) :
    mkt.completenessDepth = ⊤ ∧
      ∀ N : ℕ, (mkt.sigSpan N).topologicalClosure ≠ mkt.L2S :=
  ⟨mkt.completenessDepth_eq_top_of_not_finiteDimensional hinf,
    mkt.sigSpan_ne_L2S_of_not_finiteDimensional hinf⟩

/-- **Theorem C, right-hand side, for Black–Scholes.** It fails at every finite depth. -/
theorem theorem_C_blackScholes_depth_infinite (T s₀ σ₀ : ℝ) (hT : 0 < T) (hs₀ : 0 < s₀)
    (hσ₀ : σ₀ ≠ 0) (B : MultiBrownian Ω P 1) :
    (blackScholesMarket T s₀ σ₀ hT hs₀ hσ₀ B).completenessDepth = ⊤ ∧
      ∀ N : ℕ, ((blackScholesMarket T s₀ σ₀ hT hs₀ hσ₀ B).sigSpan N).topologicalClosure ≠
        (blackScholesMarket T s₀ σ₀ hT hs₀ hσ₀ B).L2S :=
  theorem_C_depth_infinite _ (blackScholesMarket_not_finiteDimensional_L2S T s₀ σ₀ hT hs₀ hσ₀ B)

end SignatureVolatility
