module

public import SignatureVolatility.ExtTensorAlgebra.ExtTensorAlgebra
public import SignatureVolatility.MemTw
public import SignatureVolatility.NormW
public import SignatureVolatility.RiccatiOpBounded
public import SignatureVolatility.Weight


@[expose] public section

noncomputable section

open Set

namespace SignatureVolatility

/-- A classical solution `ψ` on `[0, T]` of the Riccati equation `ψ' = R(ψ)`, `ψ(0) = u₀`: each
`ψ t ∈ T^w`, uniformly `‖·‖_w`-bounded, with each coefficient satisfying the integral equation
with a continuous integrand. -/
structure ClassicalRiccatiSolution {d : ℕ} (w : Weight) (T : ℝ)
    (R_op : ExtTensorAlgebra (d + 1) → ExtTensorAlgebra (d + 1))
    (u₀ : ExtTensorAlgebra (d + 1)) where
  ψ : ℝ → ExtTensorAlgebra (d + 1)
  mem_Tw : ∀ t ∈ Icc 0 T, MemTw w (ψ t)
  uniform_bdd : ∃ M : ℝ, 0 ≤ M ∧ ∀ t ∈ Icc 0 T, normW w (ψ t) ≤ M
  init : ψ 0 = u₀
  integral_eq : ∀ t ∈ Icc 0 T, ∀ I : Word (d + 1),
    ContinuousOn (fun s => (R_op (ψ s)).coeff I) (Icc 0 T) ∧
      (ψ t).coeff I = u₀.coeff I + ∫ s in (0 : ℝ)..t, (R_op (ψ s)).coeff I

end SignatureVolatility
