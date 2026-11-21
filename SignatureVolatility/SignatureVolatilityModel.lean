import SignatureVolatility.Weight
import SignatureVolatility.ExtTensorAlgebra.ExtTensorAlgebra
import SignatureVolatility.HypH1
import SignatureVolatility.HypH2
import SignatureVolatility.HypH3


open scoped BigOperators Classical ENNReal NNReal RealInnerProductSpace
open MeasureTheory Filter Topology Set

noncomputable section

namespace SignatureVolatility

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
  h3 : HypH3 hd ℓ


end SignatureVolatility
