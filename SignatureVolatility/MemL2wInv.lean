import SignatureVolatility.Weight
import SignatureVolatility.ExtTensorAlgebra.ExtTensorAlgebra
import SignatureVolatility.ExtTensorAlgebra.LevelNormSq


open scoped BigOperators Classical ENNReal NNReal RealInnerProductSpace
open MeasureTheory Filter Topology Set

noncomputable section

namespace SignatureVolatility

def MemL2wInv {d : ℕ} (w : Weight) (a : ExtTensorAlgebra d) : Prop :=
  Summable (fun n : ℕ => (w n) ^ 2 * a.levelNormSq n)

end SignatureVolatility
