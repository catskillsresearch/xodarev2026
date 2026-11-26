# Theorem A — global existence, uniqueness, and strict positivity

@import "TheoremA_ailean.txt" {code_block=false}

Paper: Xodarev Theorem A. Under H1–H3 the SDE $dS_t = S_t\langle\ell,\widehat W_t\rangle\,dB_t$, $S_0=s_0>0$, admits a unique global strong solution on $[0,T]$, strictly positive, with square-integrable supremum, represented as the Doléans–Dade exponential of the signature volatility.

The library theorem `theorem_A` packages this as a `SignaturePriceSolution`, whose Doléans representation holds at every outcome. The compared theorem `theorem_A_unwrapped` uses the predicate `IsSignaturePrice`: the process starts at $s_0$, is measurable and adapted to the signature filtration, is strictly positive, has almost surely continuous paths on $[0,T]$, agrees almost surely at each $t\in[0,T]$ with the Doléans exponential $s_0\exp(\mathrm{kitItoInt}\,\sigma_t - \tfrac12\mathrm{kitQuadVar}\,\sigma_t)$, satisfies the integral equation almost surely at each time, has a square-integrable supremum, and is a martingale on the signature filtration. Uniqueness is among processes that are measurable with respect to the signature filtration, lie in `KitStrongSolutionClass`, and satisfy the integral equation, up to modification on $[0,T]$. The witness is a continuous version of the packaged Doléans exponential.

The argument uses the Novikov–Doob $L^2$ martingale property, stopped $L^2$ localisation, and a pathwise Gronwall uniqueness lemma.

@import "../../SignatureVolatility/TheoremA.lean"
