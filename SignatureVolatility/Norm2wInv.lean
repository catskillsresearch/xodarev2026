module

public import SignatureVolatility.Weight
public import SignatureVolatility.ExtTensorAlgebra.ExtTensorAlgebra
public import SignatureVolatility.ExtTensorAlgebra.LevelNormSq


@[expose] public section

noncomputable section

namespace SignatureVolatility

def norm2wInv {d : ℕ} (w : Weight) (a : ExtTensorAlgebra d) : ℝ :=
  Real.sqrt (∑' n : ℕ, (w n) ^ 2 * a.levelNormSq n)

namespace norm2wInv

lemma nonneg {d : ℕ} (w : Weight) (a : ExtTensorAlgebra d) : 0 ≤ norm2wInv w a :=
  Real.sqrt_nonneg _

end norm2wInv

end SignatureVolatility
