module

public import SignatureVolatility.ExtTensorAlgebra.ExtTensorAlgebra
public import SignatureVolatility.ExtTensorAlgebra.LevelInner


@[expose] public section

noncomputable section

namespace SignatureVolatility

/-- The dual pairing `⟨ℓ, a⟩ = ∑_n ∑_{|I| = n} ℓ_I a_I` (a `tsum` over levels). -/
def dualPairing {d : ℕ} (ℓ a : ExtTensorAlgebra d) : ℝ :=
  ∑' n : ℕ, ℓ.levelInner a n

end SignatureVolatility
