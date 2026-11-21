import SignatureVolatility.ExtTensorAlgebra.IsFinitelySupported


open scoped BigOperators Classical ENNReal NNReal RealInnerProductSpace
open MeasureTheory Filter Topology Set

noncomputable section

namespace SignatureVolatility

namespace ExtTensorAlgebra

abbrev FreeTensorAlgebra (d : ℕ) := {a : ExtTensorAlgebra d // IsFinitelySupported a}

end ExtTensorAlgebra

end SignatureVolatility
