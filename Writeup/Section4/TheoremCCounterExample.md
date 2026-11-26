# Refutation of the unconditional completeness equivalence

@import "TheoremCCounterExample_ailean.txt" {code_block=false}

Paper: the unconditional form of the completeness-depth equivalence, that for an arbitrary finite strike set the market of $S$ plus those calls is complete on $\mathcal F^S_T$ if and only if $N_S^\ast<\infty$. That unrestricted equivalence, and the paper's separate claim that Black--Scholes has depth $N_S^\ast=0$, fail: Black--Scholes is complete, yet Definition 55 gives $N_S^\ast=\infty$. This is not a counterexample inside Theorem 56's finite-polynomial subcase $K(N_S^\ast)<\infty$ with a sufficiently rich strike set.

@import "../../SignatureVolatility/TheoremCCounterExample.lean"
