module

public import SignatureVolatility.Weight
public import SignatureVolatility.ExtTensorAlgebra.ExtTensorAlgebra
public import SignatureVolatility.ExtTensorAlgebra.LevelNormSq


@[expose] public section

noncomputable section

namespace SignatureVolatility

/-- `ℓ ∈ ℓ²_w`: `∑_n ‖ℓ^{(n)}‖² / w_n² < ∞`. -/
def MemL2w {d : ℕ} (w : Weight) (ℓ : ExtTensorAlgebra d) : Prop :=
  Summable (fun n : ℕ => ℓ.levelNormSq n / (w n) ^ 2)

end SignatureVolatility
