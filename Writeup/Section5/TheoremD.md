# Theorem D — hedging-error decomposition

@import "TheoremD_ailean.txt" {code_block=false}

Paper: Xodarev Theorem D. For every square-integrable price-filtration claim $X$:

1. unique orthogonal split $X=\mathbb E[X]+\int H\,dS+\varepsilon_T$ with Pythagorean identity; 2. quantitative weight-ratio tail bound for signature payoffs in a weighted class (truncate with `projLe` / `projGt`, control the tail by $\rho_N$; the weight-tail estimate lives in §1 as `TailNorm2wInvLeRatioMulNormW`); 3. if $\mathcal V_\infty=\top$ and $N\ge N_S^\ast$, then every $X$ lies in $\mathcal H_0\vee\mathcal V_N$ (depth duality with Theorem C).

Uses `GKWDecompositionSetup.replicable_hasOrthProj` and `replicableStarProjection` for the Hilbert projection; part (3) reuses the completeness-depth witness pattern from Theorem C. Entry point: `theorem_D`.

@import "../../SignatureVolatility/TheoremD.lean"
