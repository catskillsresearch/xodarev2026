import SignatureVolatility.MemTw


noncomputable section

namespace SignatureVolatility

abbrev Tw (d : ℕ) (w : Weight) := {a : ExtTensorAlgebra d // MemTw w a}

end SignatureVolatility
