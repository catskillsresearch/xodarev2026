module

public import SignatureVolatility.ExtTensorAlgebra.LevelNormSq
public import SignatureVolatility.ExtTensorAlgebra.Concat
public import SignatureVolatility.WordsOfLength
public import SignatureVolatility.Preliminaries


@[expose] public section

noncomputable section

namespace SignatureVolatility

namespace ExtTensorAlgebra

def levelNorm {d : ℕ} (a : ExtTensorAlgebra d) (n : ℕ) : ℝ :=
  Real.sqrt (levelNormSq a n)

namespace levelNorm

lemma nonneg {d : ℕ} (a : ExtTensorAlgebra d) (n : ℕ) :
    0 ≤ levelNorm a n :=
  Real.sqrt_nonneg _

lemma sq {d : ℕ} (a : ExtTensorAlgebra d) (n : ℕ) :
    (levelNorm a n) ^ 2 = levelNormSq a n :=
  Real.sq_sqrt (ExtTensorAlgebra.levelNormSq.nonneg a n)

lemma add_le {d : ℕ} (a b : ExtTensorAlgebra d) (n : ℕ) :
    levelNorm (a + b) n ≤ levelNorm a n + levelNorm b n :=
  sqrt_sum_add_sq_le (wordsOfLength d n) a.coeff b.coeff

lemma sub_eq_neg {d : ℕ} (a b : ExtTensorAlgebra d) (n : ℕ) :
    levelNorm (a - b) n = levelNorm (b - a) n := by
  unfold levelNorm levelNormSq
  congr 1
  refine Finset.sum_congr rfl fun I _ => ?_
  change (a.coeff I - b.coeff I) ^ 2 = (b.coeff I - a.coeff I) ^ 2
  ring

lemma smul {d : ℕ} (c : ℝ) (a : ExtTensorAlgebra d) (n : ℕ) :
    levelNorm (c • a) n = |c| * levelNorm a n := by
  unfold levelNorm levelNormSq
  have h : ∑ I ∈ wordsOfLength d n, (c * a.coeff I) ^ 2 =
      c ^ 2 * ∑ I ∈ wordsOfLength d n, a.coeff I ^ 2 := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun I _ => by ring
  change Real.sqrt (∑ I ∈ wordsOfLength d n, (c * a.coeff I) ^ 2) = _
  rw [h, Real.sqrt_mul (sq_nonneg c), Real.sqrt_sq_eq_abs]

lemma concat_le {d : ℕ} (a b : ExtTensorAlgebra d) (n : ℕ) :
    levelNorm (a ⊗ₜ b) n ≤
      ∑ k ∈ Finset.range (n + 1), levelNorm a k * levelNorm b (n - k) := by
  have hrew : levelNormSq (a ⊗ₜ b) n =
      ∑ I ∈ wordsOfLength d n,
        (∑ k ∈ Finset.range (n + 1), a.coeff (I.take k) * b.coeff (I.drop k)) ^ 2 := by
    unfold levelNormSq concat
    refine Finset.sum_congr rfl fun I hI => ?_
    have hlen : I.length = n := wordsOfLength.mem.mp hI
    simp [hlen]
  unfold levelNorm
  rw [hrew]
  refine (sqrt_sum_finset_sum_sq_le (wordsOfLength d n) (Finset.range (n + 1))
    (fun k I => a.coeff (I.take k) * b.coeff (I.drop k))).trans ?_
  refine Finset.sum_le_sum fun k hk => ?_
  have hkn : k ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
  rw [wordsOfLength.take_drop_sq d k n hkn a.coeff b.coeff,
    Real.sqrt_mul (Finset.sum_nonneg fun _ _ => sq_nonneg _)]
  rfl

end levelNorm

end ExtTensorAlgebra

end SignatureVolatility
