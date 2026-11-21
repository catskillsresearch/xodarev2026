import SignatureVolatility.ExtTensorAlgebra.ExtTensorAlgebra
import SignatureVolatility.Letter
import SignatureVolatility.Word


open scoped BigOperators Classical ENNReal NNReal RealInnerProductSpace
open MeasureTheory Filter Topology Set

noncomputable section

namespace SignatureVolatility

def projLe {d : ℕ} (N : ℕ) (a : ExtTensorAlgebra d) : ExtTensorAlgebra d :=
  ⟨fun I => if I.length ≤ N then a.coeff I else 0⟩

end SignatureVolatility
