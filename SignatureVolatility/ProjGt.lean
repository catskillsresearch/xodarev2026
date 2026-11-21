import SignatureVolatility.ExtTensorAlgebra.ExtTensorAlgebra
import SignatureVolatility.ExtTensorAlgebra.LevelNorm
import SignatureVolatility.ExtTensorAlgebra.LevelNormSq
import SignatureVolatility.ProjLe
import SignatureVolatility.Letter
import SignatureVolatility.Word


open scoped BigOperators Classical ENNReal NNReal RealInnerProductSpace
open MeasureTheory Filter Topology Set

noncomputable section

namespace SignatureVolatility

def projGt {d : ℕ} (N : ℕ) (a : ExtTensorAlgebra d) : ExtTensorAlgebra d :=
  ⟨fun I => if N < I.length then a.coeff I else 0⟩

namespace projGt

lemma add_projLe {d : ℕ} (N : ℕ) (a : ExtTensorAlgebra d) :
    projLe N a + projGt N a = a := by
  ext I
  change (if I.length ≤ N then a.coeff I else 0) + (if N < I.length then a.coeff I else 0) =
    a.coeff I
  by_cases h : I.length ≤ N
  · have hnot : ¬ N < I.length := not_lt_of_ge h
    simp [h, hnot]
  · have hlt : N < I.length := lt_of_not_ge h
    simp [h, hlt]

lemma levelNormSq {d : ℕ} (N : ℕ) (a : ExtTensorAlgebra d) (n : ℕ) :
    (projGt N a).levelNormSq n = if N < n then a.levelNormSq n else 0 := by
  unfold ExtTensorAlgebra.levelNormSq projGt
  split_ifs with h
  · refine Finset.sum_congr rfl fun I hI => ?_
    rw [wordsOfLength.mem.mp hI, if_pos h]
  · refine Finset.sum_eq_zero fun I hI => ?_
    rw [wordsOfLength.mem.mp hI, if_neg h]
    ring

lemma levelNorm {d : ℕ} (N : ℕ) (a : ExtTensorAlgebra d) (n : ℕ) :
    (projGt N a).levelNorm n = if N < n then a.levelNorm n else 0 := by
  unfold ExtTensorAlgebra.levelNorm
  rw [projGt.levelNormSq]
  split_ifs <;> simp

end projGt

end SignatureVolatility
