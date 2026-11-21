import SignatureVolatility.ExtTensorAlgebra.IsFinitelySupported


noncomputable section

namespace SignatureVolatility

namespace ExtTensorAlgebra

abbrev FreeTensorAlgebra (d : ℕ) := {a : ExtTensorAlgebra d // IsFinitelySupported a}

end ExtTensorAlgebra

end SignatureVolatility
