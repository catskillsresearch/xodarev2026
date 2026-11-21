module

public import SignatureVolatility.ExtTensorAlgebra.LevelNorm
public import SignatureVolatility.ExtTensorAlgebra.TensorExp


@[expose] public section

namespace SignatureVolatility

namespace ExtTensorAlgebra

/-- Summing squared letter-products over all words of length `n` gives `(∑ vᵢ²)ⁿ`. -/
lemma sum_wordsOfLength_prod_sq {d : ℕ} (v : Fin d → ℝ) (n : ℕ) :
    ∑ I ∈ wordsOfLength d n, ((I.map v).prod) ^ 2 = (∑ i, v i ^ 2) ^ n := by
  induction n with
  | zero => simp [wordsOfLength]
  | succ n ih =>
    rw [wordsOfLength.succ, pow_succ', Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← ih, Finset.mul_sum]
    refine Finset.sum_congr rfl fun J _ => ?_
    simp [mul_pow]

/-- Squared level-`n` norm of a pure level-1 exponential: `‖v‖₂^{2n} / (n!)²`. -/
lemma tensorExp_levelNormSq {d : ℕ} (v : Fin d → ℝ) (n : ℕ) :
    levelNormSq (tensorExp v) n = (∑ i, v i ^ 2) ^ n / (n.factorial : ℝ) ^ 2 := by
  unfold levelNormSq
  rw [← sum_wordsOfLength_prod_sq, Finset.sum_div]
  refine Finset.sum_congr rfl fun I hI => ?_
  have hlen : I.length = n := wordsOfLength.mem.mp hI
  simp [tensorExp, hlen, div_pow]

/-- Level-`n` norm of a pure level-1 exponential: `‖v‖₂ⁿ / n!`. -/
lemma tensorExp_levelNorm {d : ℕ} (v : Fin d → ℝ) (n : ℕ) :
    levelNorm (tensorExp v) n = Real.sqrt (∑ i, v i ^ 2) ^ n / (n.factorial : ℝ) := by
  have hS : (0 : ℝ) ≤ ∑ i, v i ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hrew : (∑ i, v i ^ 2) ^ n / (n.factorial : ℝ) ^ 2 =
      (Real.sqrt (∑ i, v i ^ 2) ^ n / (n.factorial : ℝ)) ^ 2 := by
    rw [div_pow, ← pow_mul, mul_comm, pow_mul, Real.sq_sqrt hS]
  unfold levelNorm
  rw [tensorExp_levelNormSq, hrew, Real.sqrt_sq (by positivity)]

end ExtTensorAlgebra

end SignatureVolatility
