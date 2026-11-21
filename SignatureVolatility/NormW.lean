import SignatureVolatility.Weight
import SignatureVolatility.ExtTensorAlgebra.ExtTensorAlgebra
import SignatureVolatility.ExtTensorAlgebra.LevelNorm


open scoped BigOperators Classical ENNReal NNReal RealInnerProductSpace
open MeasureTheory Filter Topology Set

noncomputable section

namespace SignatureVolatility

def normW {d : ℕ} (w : Weight) (a : ExtTensorAlgebra d) : ℝ :=
  ∑' n : ℕ, w n * a.levelNorm n

namespace normW

lemma nonneg {d : ℕ} (w : Weight) (a : ExtTensorAlgebra d) : 0 ≤ normW w a :=
  tsum_nonneg fun n => mul_nonneg (w.pos n).le (ExtTensorAlgebra.levelNorm.nonneg a n)

end normW

end SignatureVolatility
