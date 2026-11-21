import SignatureVolatility.ExtTensorAlgebra.ExtTensorAlgebra
import SignatureVolatility.ExtTensorAlgebra.LevelInner


open scoped BigOperators Classical ENNReal NNReal RealInnerProductSpace
open MeasureTheory Filter Topology Set

noncomputable section

namespace SignatureVolatility

def dualPairing {d : ℕ} (ℓ a : ExtTensorAlgebra d) : ℝ :=
  ∑' n : ℕ, ℓ.levelInner a n

end SignatureVolatility
