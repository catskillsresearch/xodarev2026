import SignatureVolatility.ExtTensorAlgebra.ExtTensorAlgebra


open scoped BigOperators Classical ENNReal NNReal RealInnerProductSpace
open MeasureTheory Filter Topology Set

noncomputable section

namespace SignatureVolatility

def stratonovichHalfLaplacian {d : ℕ} (u : ExtTensorAlgebra (d + 1)) :
    ExtTensorAlgebra (d + 1) :=
  ⟨fun I => (1 / 2 : ℝ) * ∑ i : Fin d, u.coeff (I ++ [i.succ, i.succ])⟩

end SignatureVolatility
