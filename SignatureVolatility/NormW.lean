module

public import SignatureVolatility.Weight
public import SignatureVolatility.ExtTensorAlgebra.ExtTensorAlgebra
public import SignatureVolatility.ExtTensorAlgebra.LevelNorm


@[expose] public section

noncomputable section

namespace SignatureVolatility

/-- The weighted norm `‖a‖_w = ∑_n w_n ‖a^{(n)}‖`. -/
def normW {d : ℕ} (w : Weight) (a : ExtTensorAlgebra d) : ℝ :=
  ∑' n : ℕ, w n * a.levelNorm n

namespace normW

lemma nonneg {d : ℕ} (w : Weight) (a : ExtTensorAlgebra d) : 0 ≤ normW w a :=
  tsum_nonneg fun n => mul_nonneg (w.pos n).le (ExtTensorAlgebra.levelNorm.nonneg a n)

end normW

end SignatureVolatility
