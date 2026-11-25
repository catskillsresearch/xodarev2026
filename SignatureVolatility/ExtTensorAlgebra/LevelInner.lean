module

public import SignatureVolatility.ExtTensorAlgebra.LevelNorm
public import SignatureVolatility.ExtTensorAlgebra.LevelNormSq
public import SignatureVolatility.WordsOfLength
public import SignatureVolatility.Preliminaries


@[expose] public section

noncomputable section

namespace SignatureVolatility

namespace ExtTensorAlgebra

/-- Level-`n` inner product `∑_{|I| = n} ℓ_I a_I`. -/
def levelInner {d : ℕ} (ℓ a : ExtTensorAlgebra d) (n : ℕ) : ℝ :=
  ∑ I ∈ wordsOfLength d n, ℓ.coeff I * a.coeff I

namespace levelInner

lemma abs_le {d : ℕ} (ℓ a : ExtTensorAlgebra d) (n : ℕ) :
    |levelInner ℓ a n| ≤ levelNorm ℓ n * levelNorm a n :=
  abs_finset_sum_mul_le_sqrt (wordsOfLength d n) ℓ.coeff a.coeff

end levelInner

end ExtTensorAlgebra

end SignatureVolatility
