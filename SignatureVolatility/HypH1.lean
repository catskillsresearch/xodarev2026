module

public import SignatureVolatility.MemL2w
public import SignatureVolatility.Weight
public import SignatureVolatility.ExtTensorAlgebra.ExtTensorAlgebra


@[expose] public section

noncomputable section

namespace SignatureVolatility

structure HypH1 {d : ℕ} (w : Weight) (ℓ : ExtTensorAlgebra (d + 1)) : Prop where
  mem_l2w : MemL2w w ℓ

end SignatureVolatility
