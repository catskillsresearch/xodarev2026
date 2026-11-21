import SignatureVolatility.Weight
import SignatureVolatility.ExtTensorAlgebra.ExtTensorAlgebra
import SignatureVolatility.RightShift
import SignatureVolatility.StratonovichHalfLaplacian
import SignatureVolatility.ShuffleFinite


open scoped BigOperators Classical ENNReal NNReal RealInnerProductSpace
open MeasureTheory Filter Topology Set

noncomputable section

namespace SignatureVolatility

def riccatiOpBounded {d : ℕ} (N : ℕ) (u : ExtTensorAlgebra (d + 1)) :
    ExtTensorAlgebra (d + 1) :=
  rightShift 0 u + stratonovichHalfLaplacian u +
    (1 / 2 : ℝ) • ∑ i : Fin d, shuffleFinite (rightShift i.succ u) (rightShift i.succ u) N

end SignatureVolatility
