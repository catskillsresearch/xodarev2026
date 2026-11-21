import SignatureVolatility.Weight
import SignatureVolatility.ExtTensorAlgebra.ExtTensorAlgebra
import SignatureVolatility.ExtTensorAlgebra.LevelNorm
import SignatureVolatility.MemTwDual


open scoped BigOperators Classical ENNReal NNReal RealInnerProductSpace
open MeasureTheory Filter Topology Set

noncomputable section

namespace SignatureVolatility

def normWDual {d : ℕ} (w : Weight) (ℓ : ExtTensorAlgebra d) : ℝ :=
  ⨆ n : ℕ, ℓ.levelNorm n / w n

namespace normWDual

lemma levelNorm_div_le {d : ℕ} (w : Weight) {ℓ : ExtTensorAlgebra d}
    (hℓ : MemTwDual w ℓ) (n : ℕ) :
    ℓ.levelNorm n / w n ≤ normWDual w ℓ :=
  le_ciSup hℓ n

lemma nonneg {d : ℕ} (w : Weight) {ℓ : ExtTensorAlgebra d} (hℓ : MemTwDual w ℓ) :
    0 ≤ normWDual w ℓ :=
  (div_nonneg (ExtTensorAlgebra.levelNorm.nonneg ℓ 0) (w.pos 0).le).trans (normWDual.levelNorm_div_le w hℓ 0)

end normWDual

end SignatureVolatility
