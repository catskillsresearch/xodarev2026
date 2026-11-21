import SignatureVolatility.ExtTensorAlgebra.ShuffleWords
import SignatureVolatility.ExtTensorAlgebra.ExtTensorAlgebra


noncomputable section

namespace SignatureVolatility

namespace ExtTensorAlgebra

def shuffleBasis {d : ℕ} (I J : Word d) : ExtTensorAlgebra d :=
  ⟨fun K => ((shuffleWords I J).map fun L => if K = L then (1 : ℝ) else 0).sum⟩

end ExtTensorAlgebra

end SignatureVolatility
