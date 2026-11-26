module

public import SignatureVolatility.TheoremCCounterExample

@[expose] public section

open MeasureTheory

namespace SignatureVolatility

/-!
# Price-filtration completeness depth (paper Theorem C / Theorem 56)

**Definition 55.** `N^*_S` is the least `N` for which
`closure span{⟨e_I, Ŵ_T⟩ : |I| ≤ N} ∩ L²(ℱ^S_T)` equals `L²(ℱ^S_T)`, and is `∞` if no such
finite `N` exists (the paper also requires `K(N) < ∞` in that proviso).

**Theorem 56** restricts the completeness-depth equivalence to the finite-polynomial subcase
`K(N^*_S) < ∞` and to a strike set rich enough to span polynomials in `S_T` of degree at most
`K(N^*_S)`. The **unconditional** form of the equivalence — that for an arbitrary finite strike
set, the market of `S` plus those calls is complete on `ℱ^S_T` iff `N^*_S < ∞` — is a stronger
claim, and is the claim formalized here.

**What is true.** Each depth-`N` span is finite-dimensional. Hence `N^*_S < ∞` holds only when
`L²(ℱ^S_T)` is finite-dimensional. In every non-degenerate model, `N^*_S = ∞` and no finite
depth is dense (`theorem_C_depth_infinite`). This includes Black–Scholes
(`theorem_C_blackScholes_depth_infinite`), so the paper's separate Proposition 58 claim
`N^*_S = 0` is false (`not_prop58_blackScholes_depth_zero`).

The unconditional equivalence is therefore false: Black–Scholes is complete on `ℱ^S_T`
(Brownian martingale representation on `ℱ^S = ℱ^W`, `blackScholes_isCompleteWithCalls`) while
`N^*_S = ∞`. This is not a counterexample inside Theorem 56's finite-polynomial, rich-strike
hypotheses, because the Black–Scholes witness has `N^*_S = ∞` under Definition 55.

**CounterExample_TheoremC** (`theorem_C_refuted`, proved in `TheoremCCounterExample`): for the
Black–Scholes market and every finite strike set, the unconditional equivalence
"complete ⇔ `N^*_S < ∞`" is false, and the paper's Black–Scholes depth claim fails.
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

/-- **Unconditional completeness iff and Black–Scholes depth.** The unconditional equivalence
"complete with finitely many calls ⇔ `N^*_S < ∞`" (any finite strike set) fails for Black–Scholes,
and so does the paper's separate depth claim `N^*_S = 0`. This is not a counterexample inside
Theorem 56's finite-polynomial subcase `K(N^*_S) < ∞` with a sufficiently rich strike set. -/
theorem theorem_C_refuted (T s₀ σ₀ : ℝ) (hT : 0 < T) (hs₀ : 0 < s₀) (hσ₀ : σ₀ ≠ 0)
    (B : MultiBrownian Ω P 1) (strikes : Finset ℝ) :
    ¬ (IsCompleteWithCalls T s₀ σ₀ hT hs₀ hσ₀ B strikes ↔
      (blackScholesMarket T s₀ σ₀ hT hs₀ hσ₀ B).completenessDepth < ⊤) :=
  not_theorem_C T s₀ σ₀ hT hs₀ hσ₀ B strikes

end SignatureVolatility
