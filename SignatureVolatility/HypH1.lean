import SignatureVolatility.MemL2w
import SignatureVolatility.Weight
import SignatureVolatility.ExtTensorAlgebra.ExtTensorAlgebra


open scoped BigOperators Classical ENNReal NNReal RealInnerProductSpace
open MeasureTheory Filter Topology Set

noncomputable section

namespace SignatureVolatility

structure HypH1 {d : ℕ} (w : Weight) (ℓ : ExtTensorAlgebra (d + 1)) : Prop where
  mem_l2w : MemL2w w ℓ

end SignatureVolatility
