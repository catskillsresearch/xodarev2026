import SignatureVolatility.ExtTensorAlgebra.ExtTensorAlgebra


open scoped BigOperators Classical ENNReal NNReal RealInnerProductSpace
open MeasureTheory Filter Topology Set

noncomputable section

namespace SignatureVolatility

structure HypH3 {d : ℕ} (hd : 0 < d) (ℓ : ExtTensorAlgebra (d + 1)) : Prop where
  nonZero : ℓ ≠ 0

end SignatureVolatility
