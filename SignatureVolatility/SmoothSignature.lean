import SignatureVolatility.SmoothIteratedIntegral
import SignatureVolatility.ExtTensorAlgebra.ExtTensorAlgebra

noncomputable section

namespace SignatureVolatility

def smoothSignature {d : ℕ} (X' : ℝ → Fin d → ℝ) (s t : ℝ) : ExtTensorAlgebra d :=
  ⟨fun I => smoothIteratedIntegral X' s I t⟩

end SignatureVolatility