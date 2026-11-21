module

public import SignatureVolatility.SmoothIteratedIntegral
public import SignatureVolatility.ExtTensorAlgebra.ExtTensorAlgebra


@[expose] public section

noncomputable section

namespace SignatureVolatility

def smoothSignature {d : ℕ} (X' : ℝ → Fin d → ℝ) (s t : ℝ) : ExtTensorAlgebra d :=
  ⟨fun I => smoothIteratedIntegral X' s I t⟩

end SignatureVolatility
