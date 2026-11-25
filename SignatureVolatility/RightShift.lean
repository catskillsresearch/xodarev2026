module

public import SignatureVolatility.ExtTensorAlgebra.ExtTensorAlgebra


@[expose] public section

namespace SignatureVolatility

/-- Right shift by the letter `k`: `(rightShift k u)_I = u_{I k}`. -/
def rightShift {d : ℕ} (k : Letter (d + 1)) (u : ExtTensorAlgebra (d + 1)) :
    ExtTensorAlgebra (d + 1) :=
  ⟨fun I => u.coeff (I ++ [k])⟩

end SignatureVolatility
