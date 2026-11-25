module

public import SignatureVolatility.ExtTensorAlgebra.ExtTensorAlgebra


@[expose] public section

noncomputable section

namespace SignatureVolatility

/-- Itô–Stratonovich half-Laplacian: `(Δ u)_I = ½ ∑_{i=1}^{d} u_{I i i}` (space letters only). -/
def stratonovichHalfLaplacian {d : ℕ} (u : ExtTensorAlgebra (d + 1)) :
    ExtTensorAlgebra (d + 1) :=
  ⟨fun I => (1 / 2 : ℝ) * ∑ i : Fin d, u.coeff (I ++ [i.succ, i.succ])⟩

end SignatureVolatility
