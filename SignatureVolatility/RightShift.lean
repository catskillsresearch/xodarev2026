import SignatureVolatility.ExtTensorAlgebra.ExtTensorAlgebra

namespace SignatureVolatility

def rightShift {d : ℕ} (k : Letter (d + 1)) (u : ExtTensorAlgebra (d + 1)) :
    ExtTensorAlgebra (d + 1) :=
  ⟨fun I => u.coeff (I ++ [k])⟩

end SignatureVolatility