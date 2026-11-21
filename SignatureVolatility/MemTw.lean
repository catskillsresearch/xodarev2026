import SignatureVolatility.Weight
import SignatureVolatility.ExtTensorAlgebra.ExtTensorAlgebra
import SignatureVolatility.ExtTensorAlgebra.LevelNorm


open scoped BigOperators Classical ENNReal NNReal RealInnerProductSpace
open MeasureTheory Filter Topology Set

noncomputable section

namespace SignatureVolatility

def MemTw {d : ℕ} (w : Weight) (a : ExtTensorAlgebra d) : Prop :=
  Summable (fun n : ℕ => w n * a.levelNorm n)

end SignatureVolatility
