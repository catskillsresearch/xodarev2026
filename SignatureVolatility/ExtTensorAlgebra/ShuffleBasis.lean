module

public import SignatureVolatility.ExtTensorAlgebra.ShuffleWords
public import SignatureVolatility.ExtTensorAlgebra.ExtTensorAlgebra


@[expose] public section

noncomputable section

namespace SignatureVolatility

namespace ExtTensorAlgebra

/-- The shuffle product `e_I ⧢ e_J = ∑_{K ∈ I ⧢ J} e_K` (with multiplicity). -/
def shuffleBasis {d : ℕ} (I J : Word d) : ExtTensorAlgebra d :=
  ⟨fun K => ((shuffleWords I J).map fun L => if K = L then (1 : ℝ) else 0).sum⟩

end ExtTensorAlgebra

end SignatureVolatility
