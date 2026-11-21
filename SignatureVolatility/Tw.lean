module

public import SignatureVolatility.MemTw


@[expose] public section

noncomputable section

namespace SignatureVolatility

abbrev Tw (d : ℕ) (w : Weight) := {a : ExtTensorAlgebra d // MemTw w a}

end SignatureVolatility
