import SignatureVolatility.Weight
import SignatureVolatility.ExtTensorAlgebra.ExtTensorAlgebra
import SignatureVolatility.ExtTensorAlgebra.LevelNorm


open scoped BigOperators Classical ENNReal NNReal RealInnerProductSpace
open MeasureTheory Filter Topology Set

noncomputable section

namespace SignatureVolatility

def MemTwDual {d : ℕ} (w : Weight) (ℓ : ExtTensorAlgebra d) : Prop :=
  BddAbove (Set.range fun n : ℕ => ℓ.levelNorm n / w n)

end SignatureVolatility
