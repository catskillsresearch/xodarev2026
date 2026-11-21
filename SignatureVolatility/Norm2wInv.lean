import SignatureVolatility.Weight
import SignatureVolatility.ExtTensorAlgebra.ExtTensorAlgebra
import SignatureVolatility.ExtTensorAlgebra.LevelNormSq


noncomputable section

namespace SignatureVolatility

def norm2wInv {d : ℕ} (w : Weight) (a : ExtTensorAlgebra d) : ℝ :=
  Real.sqrt (∑' n : ℕ, (w n) ^ 2 * a.levelNormSq n)

namespace norm2wInv

lemma nonneg {d : ℕ} (w : Weight) (a : ExtTensorAlgebra d) : 0 ≤ norm2wInv w a :=
  Real.sqrt_nonneg _

end norm2wInv

end SignatureVolatility
