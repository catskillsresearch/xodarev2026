import SignatureVolatility.Weight
import SignatureVolatility.ExtTensorAlgebra.ExtTensorAlgebra
import SignatureVolatility.ExtTensorAlgebra.LevelNormSq


open scoped BigOperators Classical ENNReal NNReal RealInnerProductSpace
open MeasureTheory Filter Topology Set

noncomputable section

namespace SignatureVolatility

def norm2w {d : ℕ} (w : Weight) (ℓ : ExtTensorAlgebra d) : ℝ :=
  Real.sqrt (∑' n : ℕ, ℓ.levelNormSq n / (w n) ^ 2)

namespace norm2w

lemma nonneg {d : ℕ} (w : Weight) (ℓ : ExtTensorAlgebra d) : 0 ≤ norm2w w ℓ :=
  Real.sqrt_nonneg _

end norm2w

end SignatureVolatility
