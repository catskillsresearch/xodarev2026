import SignatureVolatility.ExtTensorAlgebra.ShuffleWords
import SignatureVolatility.ExtTensorAlgebra.ExtTensorAlgebra


noncomputable section

namespace SignatureVolatility

namespace ExtTensorAlgebra

def evalShuffleBasis {d : ℕ} (I J : Word d) (X : ExtTensorAlgebra d) : ℝ :=
  ((shuffleWords I J).map fun K => X.coeff K).sum

end ExtTensorAlgebra

end SignatureVolatility
