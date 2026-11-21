import SignatureVolatility.Weight
import SignatureVolatility.ExtTensorAlgebra.ExtTensorAlgebra
import SignatureVolatility.ExtTensorAlgebra.LevelNormSq


noncomputable section

namespace SignatureVolatility

def MemL2wInv {d : ℕ} (w : Weight) (a : ExtTensorAlgebra d) : Prop :=
  Summable (fun n : ℕ => (w n) ^ 2 * a.levelNormSq n)

end SignatureVolatility
