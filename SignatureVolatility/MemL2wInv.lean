module

public import SignatureVolatility.Weight
public import SignatureVolatility.ExtTensorAlgebra.ExtTensorAlgebra
public import SignatureVolatility.ExtTensorAlgebra.LevelNormSq


@[expose] public section

noncomputable section

namespace SignatureVolatility

def MemL2wInv {d : ℕ} (w : Weight) (a : ExtTensorAlgebra d) : Prop :=
  Summable (fun n : ℕ => (w n) ^ 2 * a.levelNormSq n)

end SignatureVolatility
