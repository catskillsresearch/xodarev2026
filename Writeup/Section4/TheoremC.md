# Theorem C — completeness depth on $\mathcal F^S$

@import "TheoremC_ailean.txt" {code_block=false}

Paper: Xodarev Theorem C. For dense strike sets $\mathcal K_1,\mathcal K_2\subset(0,\infty)$, augmented completeness at level $N$ is equivalent to $N_S^\ast\le N$, no smaller level completes the market, and the completeness predicate is independent of the chosen dense strike set (Davis–Obłój bridge).

Depth is `sInf` of levels whose truncated signature span closes to $\mathcal V_\infty$. The reverse implication uses `csInf_mem` on $\mathbb N^\infty$ and monotonicity of `V_subspace`, with `not_top_le_coe` ruling out an empty realizing set. Entry point: `theorem_C`.

@import "../../SignatureVolatility/TheoremC.lean"
