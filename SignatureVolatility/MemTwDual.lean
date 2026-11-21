module

public import SignatureVolatility.Weight
public import SignatureVolatility.ExtTensorAlgebra.ExtTensorAlgebra
public import SignatureVolatility.ExtTensorAlgebra.LevelNorm


@[expose] public section

noncomputable section

namespace SignatureVolatility

def MemTwDual {d : ℕ} (w : Weight) (ℓ : ExtTensorAlgebra d) : Prop :=
  BddAbove (Set.range fun n : ℕ => ℓ.levelNorm n / w n)

end SignatureVolatility
