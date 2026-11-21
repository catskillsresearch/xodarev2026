import SignatureVolatility.SmoothIteratedIntegral
import SignatureVolatility.ExtTensorAlgebra.ExtTensorAlgebra


open scoped BigOperators Classical ENNReal NNReal RealInnerProductSpace
open MeasureTheory Filter Topology Set

noncomputable section

namespace SignatureVolatility

def smoothSignature {d : ℕ} (X' : ℝ → Fin d → ℝ) (s t : ℝ) : ExtTensorAlgebra d :=
  ⟨fun I => smoothIteratedIntegral X' s I t⟩

end SignatureVolatility
