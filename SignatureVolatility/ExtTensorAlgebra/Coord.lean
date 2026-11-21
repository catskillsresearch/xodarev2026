module

public import SignatureVolatility.ExtTensorAlgebra.ExtTensorAlgebra


@[expose] public section

namespace SignatureVolatility

namespace ExtTensorAlgebra

def coord {d : ℕ} (I : Word d) (a : ExtTensorAlgebra d) : ℝ :=
  a.coeff I

end ExtTensorAlgebra

end SignatureVolatility
