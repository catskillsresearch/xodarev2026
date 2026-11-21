import SignatureVolatility.ExtTensorAlgebra.ExtTensorAlgebra

noncomputable section

namespace SignatureVolatility

def stratonovichHalfLaplacian {d : ℕ} (u : ExtTensorAlgebra (d + 1)) :
    ExtTensorAlgebra (d + 1) :=
  ⟨fun I => (1 / 2 : ℝ) * ∑ i : Fin d, u.coeff (I ++ [i.succ, i.succ])⟩

end SignatureVolatility