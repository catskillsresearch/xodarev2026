import SignatureVolatility.ExtTensorAlgebra.ExtTensorAlgebra
import SignatureVolatility.WordsOfLength
import SignatureVolatility.Letter
import SignatureVolatility.Word


open scoped BigOperators Classical ENNReal NNReal RealInnerProductSpace
open MeasureTheory Filter Topology Set

noncomputable section

namespace SignatureVolatility

namespace ExtTensorAlgebra

def levelNormSq {d : ℕ} (a : ExtTensorAlgebra d) (n : ℕ) : ℝ :=
  ∑ I ∈ wordsOfLength d n, (a.coeff I) ^ 2

namespace levelNormSq

lemma nonneg {d : ℕ} (a : ExtTensorAlgebra d) (n : ℕ) :
    0 ≤ levelNormSq a n :=
  Finset.sum_nonneg fun _ _ => sq_nonneg _

end levelNormSq

end ExtTensorAlgebra

end SignatureVolatility
