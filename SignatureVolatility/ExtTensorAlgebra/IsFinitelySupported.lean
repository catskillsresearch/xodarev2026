import SignatureVolatility.ExtTensorAlgebra.ExtTensorAlgebra

namespace SignatureVolatility

namespace ExtTensorAlgebra

def IsFinitelySupported {d : ℕ} (a : ExtTensorAlgebra d) : Prop :=
  ∃ N : ℕ, ∀ I : Word d, N < I.length → a.coeff I = 0

end ExtTensorAlgebra

end SignatureVolatility