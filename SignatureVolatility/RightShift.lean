import SignatureVolatility.ExtTensorAlgebra.ExtTensorAlgebra
import SignatureVolatility.Letter
import SignatureVolatility.Word


open scoped BigOperators Classical ENNReal NNReal RealInnerProductSpace
open MeasureTheory Filter Topology Set

noncomputable section

namespace SignatureVolatility

def rightShift {d : ℕ} (k : Letter (d + 1)) (u : ExtTensorAlgebra (d + 1)) :
    ExtTensorAlgebra (d + 1) :=
  ⟨fun I => u.coeff (I ++ [k])⟩

end SignatureVolatility
