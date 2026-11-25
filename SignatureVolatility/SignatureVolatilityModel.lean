module

public import SignatureVolatility.Weight
public import SignatureVolatility.ExtTensorAlgebra.ExtTensorAlgebra
public import SignatureVolatility.HypH1
public import SignatureVolatility.HypH2
public import SignatureVolatility.HypH3


@[expose] public section

open scoped BigOperators Classical ENNReal NNReal RealInnerProductSpace
open MeasureTheory Filter Topology Set

noncomputable section

namespace SignatureVolatility

/-- A signature volatility model: `d ≥ 1` Brownian coordinates, horizon `T > 0`, weight `w`,
volatility functional `ℓ ∈ T((ℝ^{d+1}))`, initial price `s₀ > 0`, and hypotheses H1, H2 and
`ℓ ≠ 0`. -/
structure SignatureVolatilityModel where
  d : ℕ
  hd : 0 < d
  T : ℝ
  hT : 0 < T
  w : Weight
  ℓ : ExtTensorAlgebra (d + 1)
  s₀ : ℝ
  hs₀ : 0 < s₀
  h1 : HypH1 w ℓ
  h2 : HypH2 w
  /-- Parameter nondegeneracy (`ℓ ≠ 0`). Analytic Novikov H3 on `ξ = ⟨ℓ,Ŵ⟩` is
  a separate hypothesis when inhabiting `ItoCalculusKit`. -/
  h3 : HypH3Param hd ℓ


end SignatureVolatility
