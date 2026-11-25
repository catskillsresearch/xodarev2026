module

public import SignatureVolatility.Weight
public import SignatureVolatility.ExtTensorAlgebra.ExtTensorAlgebra
public import SignatureVolatility.ExtTensorAlgebra.LevelNorm


@[expose] public section

noncomputable section

namespace SignatureVolatility

/-- `a ∈ T^w`: the weighted level norms are summable, `∑_n w_n ‖a^{(n)}‖ < ∞`. -/
def MemTw {d : ℕ} (w : Weight) (a : ExtTensorAlgebra d) : Prop :=
  Summable (fun n : ℕ => w n * a.levelNorm n)

end SignatureVolatility
