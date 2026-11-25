module

public import SignatureVolatility.ExtTensorAlgebra.IsFinitelySupported


@[expose] public section

noncomputable section

namespace SignatureVolatility

namespace ExtTensorAlgebra

/-- The free tensor algebra: the finitely supported elements of `T((ℝ^d))`. -/
abbrev FreeTensorAlgebra (d : ℕ) := {a : ExtTensorAlgebra d // IsFinitelySupported a}

end ExtTensorAlgebra

end SignatureVolatility
