module

public import SignatureVolatility.ExtTensorAlgebra.ExtTensorAlgebra
public import SignatureVolatility.WordsOfLength


@[expose] public section

namespace SignatureVolatility

namespace ExtTensorAlgebra

/-- Squared Euclidean norm of the level-`n` component: `∑_{|I| = n} a_I²`. -/
def levelNormSq {d : ℕ} (a : ExtTensorAlgebra d) (n : ℕ) : ℝ :=
  ∑ I ∈ wordsOfLength d n, (a.coeff I) ^ 2

namespace levelNormSq

lemma nonneg {d : ℕ} (a : ExtTensorAlgebra d) (n : ℕ) :
    0 ≤ levelNormSq a n :=
  Finset.sum_nonneg fun _ _ => sq_nonneg _

end levelNormSq

end ExtTensorAlgebra

end SignatureVolatility
