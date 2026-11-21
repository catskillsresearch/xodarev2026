import SignatureVolatility.ExtTensorAlgebra.ExtTensorAlgebra
import SignatureVolatility.Letter
import SignatureVolatility.Word


open scoped BigOperators Classical ENNReal NNReal RealInnerProductSpace
open MeasureTheory Filter Topology Set

noncomputable section

namespace SignatureVolatility

namespace ExtTensorAlgebra

def IsFinitelySupported {d : ℕ} (a : ExtTensorAlgebra d) : Prop :=
  ∃ N : ℕ, ∀ I : Word d, N < I.length → a.coeff I = 0

end ExtTensorAlgebra

end SignatureVolatility
