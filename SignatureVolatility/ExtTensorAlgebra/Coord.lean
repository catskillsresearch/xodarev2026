import SignatureVolatility.ExtTensorAlgebra.ExtTensorAlgebra
import SignatureVolatility.Letter
import SignatureVolatility.Word


open scoped BigOperators Classical ENNReal NNReal RealInnerProductSpace
open MeasureTheory Filter Topology Set

noncomputable section

namespace SignatureVolatility

namespace ExtTensorAlgebra

def coord {d : ℕ} (I : Word d) (a : ExtTensorAlgebra d) : ℝ :=
  a.coeff I

end ExtTensorAlgebra

end SignatureVolatility
