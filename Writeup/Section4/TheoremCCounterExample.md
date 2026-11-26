# Theorem C Counter Example

@import "TheoremCCounterExample_ailean.txt" {code_block=false}

Paper: Xodarev Theorem C. The paper's Theorem C says: the market of `S` and finitely many calls is complete on `ℱ^S_T` **iff** `N^*_S < ∞`. Black–Scholes is a counterexample: * `blackScholes_isCompleteWithCalls`: every `X ∈ L²(ℱ^S_T)` is `E X` plus a stochastic integral (Brownian martingale representation, vendored `MathFin.exists_itoIntegral_representation`), so the market is complete, for every finite strike set (no calls are even needed); * `blackScholes_completenessDepth_eq_top`: `N^*_S = ∞`. Hence `not_theorem_C`...

@import "../../SignatureVolatility/TheoremCCounterExample.lean"
