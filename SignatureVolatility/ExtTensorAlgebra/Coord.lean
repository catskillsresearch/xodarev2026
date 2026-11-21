import SignatureVolatility.ExtTensorAlgebra.ExtTensorAlgebra

namespace SignatureVolatility

namespace ExtTensorAlgebra

def coord {d : ℕ} (I : Word d) (a : ExtTensorAlgebra d) : ℝ :=
  a.coeff I

end ExtTensorAlgebra

end SignatureVolatility