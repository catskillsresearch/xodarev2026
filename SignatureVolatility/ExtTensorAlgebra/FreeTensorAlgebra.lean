module

public import SignatureVolatility.ExtTensorAlgebra.IsFinitelySupported


@[expose] public section

noncomputable section

namespace SignatureVolatility

namespace ExtTensorAlgebra

abbrev FreeTensorAlgebra (d : ℕ) := {a : ExtTensorAlgebra d // IsFinitelySupported a}

end ExtTensorAlgebra

end SignatureVolatility
