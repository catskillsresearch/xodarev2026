# Prop58 Black Scholes Depth False

@import "Prop58BlackScholesDepthFalse_ailean.txt" {code_block=false}

Paper: Xodarev Proposition 58. The paper's Proposition 58 says that "Black–Scholes has `(N^*_S, K) = (0, 1)`". Under Definition 55, `N^*_S = 0` would mean `closure span{⟨e_∅, Ŵ_T⟩} ∩ L²(ℱ^S_T) = L²(ℱ^S_T)`. Since `⟨e_∅, Ŵ_T⟩ = 1`, that says `L²(ℱ^S_T)` consists of constants only.

**[SignatureVolatility/Prop58BlackScholesDepthFalse.lean](../../SignatureVolatility/Prop58BlackScholesDepthFalse.lean)**

@import "../../SignatureVolatility/Prop58BlackScholesDepthFalse.lean"
