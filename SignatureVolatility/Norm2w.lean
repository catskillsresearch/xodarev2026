import SignatureVolatility.Weight
import SignatureVolatility.ExtTensorAlgebra.ExtTensorAlgebra
import SignatureVolatility.ExtTensorAlgebra.LevelNormSq


noncomputable section

namespace SignatureVolatility

def norm2w {d : ℕ} (w : Weight) (ℓ : ExtTensorAlgebra d) : ℝ :=
  Real.sqrt (∑' n : ℕ, ℓ.levelNormSq n / (w n) ^ 2)

namespace norm2w

lemma nonneg {d : ℕ} (w : Weight) (ℓ : ExtTensorAlgebra d) : 0 ≤ norm2w w ℓ :=
  Real.sqrt_nonneg _

end norm2w

end SignatureVolatility
