import SignatureVolatility.DualPairing
import SignatureVolatility.Norm2w
import SignatureVolatility.Norm2wInv
import SignatureVolatility.MemL2w
import SignatureVolatility.MemL2wInv
import SignatureVolatility.ProjGt
import SignatureVolatility.ExtTensorAlgebra.LevelNorm
import SignatureVolatility.ExtTensorAlgebra.LevelNormSq
import SignatureVolatility.ExtTensorAlgebra.LevelInner
import SignatureVolatility.Weight
import SignatureVolatility.Preliminaries


open scoped BigOperators Classical ENNReal NNReal RealInnerProductSpace
open MeasureTheory Filter Topology Set

noncomputable section

namespace SignatureVolatility

theorem weighted_truncation_estimates {d : ℕ} (w : Weight)
    {ℓ a : ExtTensorAlgebra d} (hℓ : MemL2w w ℓ) (ha : MemL2wInv w a) :
    (|dualPairing ℓ a| ≤ norm2w w ℓ * norm2wInv w a) ∧
    (∀ N : ℕ, MemL2w w (projGt N ℓ) ∧
      |dualPairing (projGt N ℓ) a| ≤ norm2w w (projGt N ℓ) * norm2wInv w a) := by
  have hcauchy : ∀ (L : ExtTensorAlgebra d), MemL2w w L →
      |dualPairing L a| ≤ norm2w w L * norm2wInv w a := by
    intro L hL
    have hpoint : ∀ n : ℕ,
        |L.levelInner a n| ≤ (L.levelNorm n / w n) * (w n * a.levelNorm n) := by
      intro n
      have hw : w n ≠ 0 := (w.pos n).ne'
      calc
        |L.levelInner a n| ≤ L.levelNorm n * a.levelNorm n := ExtTensorAlgebra.levelInner.abs_le L a n
        _ = (L.levelNorm n / w n) * (w n * a.levelNorm n) := by field_simp [hw]
    have hrange : ∀ M : ℕ,
        (∑ n ∈ Finset.range M, |L.levelInner a n|) ≤ norm2w w L * norm2wInv w a := by
      intro M
      calc
        ∑ n ∈ Finset.range M, |L.levelInner a n|
            ≤ ∑ n ∈ Finset.range M, (L.levelNorm n / w n) * (w n * a.levelNorm n) :=
              Finset.sum_le_sum fun n _ => hpoint n
        _ ≤ Real.sqrt (∑ n ∈ Finset.range M, (L.levelNorm n / w n) ^ 2) *
              Real.sqrt (∑ n ∈ Finset.range M, (w n * a.levelNorm n) ^ 2) := by
              have h := abs_finset_sum_mul_le_sqrt (Finset.range M)
                (fun n => L.levelNorm n / w n) (fun n => w n * a.levelNorm n)
              exact (le_abs_self _).trans h
        _ ≤ norm2w w L * norm2wInv w a := by
              refine mul_le_mul ?_ ?_ (Real.sqrt_nonneg _) (norm2w.nonneg w L)
              · apply Real.sqrt_le_sqrt
                have hrew : (∑ n ∈ Finset.range M, (L.levelNorm n / w n) ^ 2) =
                    ∑ n ∈ Finset.range M, L.levelNormSq n / (w n) ^ 2 := by
                  refine Finset.sum_congr rfl fun n _ => ?_
                  rw [div_pow, ExtTensorAlgebra.levelNorm.sq L]
                rw [hrew]
                exact hL.sum_le_tsum (Finset.range M)
                  fun n _ => div_nonneg (ExtTensorAlgebra.levelNormSq.nonneg L n) (sq_nonneg _)
              · apply Real.sqrt_le_sqrt
                have hrew : (∑ n ∈ Finset.range M, (w n * a.levelNorm n) ^ 2) =
                    ∑ n ∈ Finset.range M, (w n) ^ 2 * a.levelNormSq n := by
                  refine Finset.sum_congr rfl fun n _ => ?_
                  rw [mul_pow, ExtTensorAlgebra.levelNorm.sq a]
                rw [hrew]
                exact ha.sum_le_tsum (Finset.range M)
                  fun n _ => mul_nonneg (sq_nonneg _) (ExtTensorAlgebra.levelNormSq.nonneg a n)
    have habs : Summable (fun n : ℕ => |L.levelInner a n|) :=
      summable_of_sum_range_le (fun _ => abs_nonneg _) hrange
    calc
      |dualPairing L a| ≤ ∑' n : ℕ, |L.levelInner a n| := abs_tsum_le_of_summable_abs habs
      _ ≤ norm2w w L * norm2wInv w a := habs.tsum_le_of_sum_range_le hrange
  refine ⟨hcauchy ℓ hℓ, fun N => ?_⟩
  have htail : MemL2w w (projGt N ℓ) := by
    refine Summable.of_nonneg_of_le
      (fun n => div_nonneg (ExtTensorAlgebra.levelNormSq.nonneg (projGt N ℓ) n) (sq_nonneg _))
      (fun n => ?_) hℓ
    rw [projGt.levelNormSq]
    split_ifs
    · exact le_rfl
    · rw [zero_div]
      exact div_nonneg (ExtTensorAlgebra.levelNormSq.nonneg ℓ n) (sq_nonneg _)
  exact ⟨htail, hcauchy (projGt N ℓ) htail⟩

end SignatureVolatility
