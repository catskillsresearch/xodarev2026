module

public import SignatureVolatility.ExtTensorAlgebra.ExtTensorAlgebra


@[expose] public section

namespace SignatureVolatility

structure HypH3 {d : ℕ} (hd : 0 < d) (ℓ : ExtTensorAlgebra (d + 1)) : Prop where
  nonZero : ℓ ≠ 0

end SignatureVolatility
