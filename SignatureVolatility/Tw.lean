import SignatureVolatility.MemTw


open scoped BigOperators Classical ENNReal NNReal RealInnerProductSpace
open MeasureTheory Filter Topology Set

noncomputable section

namespace SignatureVolatility

abbrev Tw (d : ℕ) (w : Weight) := {a : ExtTensorAlgebra d // MemTw w a}

end SignatureVolatility
