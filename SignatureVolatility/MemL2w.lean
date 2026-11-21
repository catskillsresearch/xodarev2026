import SignatureVolatility.Weight
import SignatureVolatility.ExtTensorAlgebra.ExtTensorAlgebra
import SignatureVolatility.ExtTensorAlgebra.LevelNormSq


open scoped BigOperators Classical ENNReal NNReal RealInnerProductSpace
open MeasureTheory Filter Topology Set

noncomputable section

namespace SignatureVolatility

def MemL2w {d : ℕ} (w : Weight) (ℓ : ExtTensorAlgebra d) : Prop :=
  Summable (fun n : ℕ => ℓ.levelNormSq n / (w n) ^ 2)

end SignatureVolatility
