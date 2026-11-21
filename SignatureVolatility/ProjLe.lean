import SignatureVolatility.ExtTensorAlgebra.ExtTensorAlgebra

namespace SignatureVolatility

def projLe {d : ℕ} (N : ℕ) (a : ExtTensorAlgebra d) : ExtTensorAlgebra d :=
  ⟨fun I => if I.length ≤ N then a.coeff I else 0⟩

end SignatureVolatility