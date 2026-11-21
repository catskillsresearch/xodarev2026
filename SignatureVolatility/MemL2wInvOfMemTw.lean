import SignatureVolatility.MemL2wInv
import SignatureVolatility.MemTw
import SignatureVolatility.Norm2wInv
import SignatureVolatility.NormW
import SignatureVolatility.Weight
import SignatureVolatility.ExtTensorAlgebra.LevelNorm
import SignatureVolatility.ExtTensorAlgebra.LevelNormSq
import SignatureVolatility.Preliminaries


open scoped BigOperators Classical ENNReal NNReal RealInnerProductSpace
open MeasureTheory Filter Topology Set

noncomputable section

namespace SignatureVolatility

lemma memL2wInv_of_memTw {d : ℕ} (w : Weight) {a : ExtTensorAlgebra d} (ha : MemTw w a) :
    MemL2wInv w a ∧ norm2wInv w a ≤ normW w a := by
  have hterm : ∀ n : ℕ, 0 ≤ (w n) ^ 2 * a.levelNormSq n :=
    fun n => mul_nonneg (sq_nonneg _) (ExtTensorAlgebra.levelNormSq.nonneg a n)
  have hrange : ∀ N : ℕ,
      (∑ n ∈ Finset.range N, (w n) ^ 2 * a.levelNormSq n) ≤ (normW w a) ^ 2 := by
    intro N
    have hrew : (∑ n ∈ Finset.range N, (w n) ^ 2 * a.levelNormSq n) =
        ∑ n ∈ Finset.range N, (w n * a.levelNorm n) ^ 2 := by
      refine Finset.sum_congr rfl fun n _ => ?_
      rw [mul_pow, ExtTensorAlgebra.levelNorm.sq a]
    rw [hrew]
    calc
      ∑ n ∈ Finset.range N, (w n * a.levelNorm n) ^ 2
          ≤ (∑ n ∈ Finset.range N, w n * a.levelNorm n) ^ 2 :=
            sum_sq_le_sq_sum (Finset.range N) (fun n => w n * a.levelNorm n)
              (fun n _ => mul_nonneg (w.pos n).le (ExtTensorAlgebra.levelNorm.nonneg a n))
      _ ≤ (normW w a) ^ 2 := by
            have hle : ∑ n ∈ Finset.range N, w n * a.levelNorm n ≤ normW w a :=
              ha.sum_le_tsum (Finset.range N)
                fun n _ => mul_nonneg (w.pos n).le (ExtTensorAlgebra.levelNorm.nonneg a n)
            exact pow_le_pow_left₀
              (Finset.sum_nonneg fun n _ => mul_nonneg (w.pos n).le (ExtTensorAlgebra.levelNorm.nonneg a n)) hle 2
  have hsum : MemL2wInv w a := summable_of_sum_range_le hterm hrange
  refine ⟨hsum, ?_⟩
  have htsum : (∑' n : ℕ, (w n) ^ 2 * a.levelNormSq n) ≤ (normW w a) ^ 2 :=
    hsum.tsum_le_of_sum_range_le hrange
  exact (Real.sqrt_le_sqrt htsum).trans_eq (Real.sqrt_sq (normW.nonneg w a))

/-! ## Section 2.6: Truncation Operators `π_N`, `π_{> N}` and Lemma 2.22 -/

end SignatureVolatility
