import SignatureVolatility.ExtTensorAlgebra.LevelNorm
import SignatureVolatility.ExtTensorAlgebra.LevelNormSq
import SignatureVolatility.WordsOfLength
import SignatureVolatility.Preliminaries


open scoped BigOperators Classical ENNReal NNReal RealInnerProductSpace
open MeasureTheory Filter Topology Set

noncomputable section

namespace SignatureVolatility

namespace ExtTensorAlgebra

def levelInner {d : ℕ} (ℓ a : ExtTensorAlgebra d) (n : ℕ) : ℝ :=
  ∑ I ∈ wordsOfLength d n, ℓ.coeff I * a.coeff I

namespace levelInner

lemma abs_le {d : ℕ} (ℓ a : ExtTensorAlgebra d) (n : ℕ) :
    |levelInner ℓ a n| ≤ levelNorm ℓ n * levelNorm a n :=
  abs_finset_sum_mul_le_sqrt (wordsOfLength d n) ℓ.coeff a.coeff

end levelInner

end ExtTensorAlgebra

end SignatureVolatility
