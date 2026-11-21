# Theorem A — global existence, uniqueness, and strict positivity

@import "TheoremA_ailean.txt" {code_block=false}

Paper: Xodarev Theorem A. Under H1–H3 the SDE $dS_t = S_t\langle\ell,\widehat W_t\rangle\,dB_t$, $S_0=s_0>0$, admits a unique global strong solution on $[0,T]$, strictly positive, with square-integrable supremum, represented as the Doléans–Dade exponential of the signature volatility.

Uses `ItoCalculusKit.novikov_doob_l2_martingale` and `stopped_l2_localisation` plus `gronwall_zero_of_continuousOn` for pathwise uniqueness of SDE solutions, and packages the output as a `SignaturePriceSolution`. Entry point: `theorem_A`.

**[SignatureVolatility/TheoremA.lean](../../SignatureVolatility/TheoremA.lean)**

@import "../../SignatureVolatility/TheoremA.lean"
