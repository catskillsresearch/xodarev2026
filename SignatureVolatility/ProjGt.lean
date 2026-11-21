module

public import SignatureVolatility.ExtTensorAlgebra.ExtTensorAlgebra
public import SignatureVolatility.ExtTensorAlgebra.LevelNorm
public import SignatureVolatility.ExtTensorAlgebra.LevelNormSq
public import SignatureVolatility.ProjLe
public import SignatureVolatility.WordsOfLength


@[expose] public section

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
    have hlen : I.length = n := (wordsOfLength.mem (d := d)).1 hI
    have hlt : N < I.length := hlen ▸ h
    simp [if_pos hlt]
  · refine Finset.sum_eq_zero fun I hI => ?_
    have hlen : I.length = n := (wordsOfLength.mem (d := d)).1 hI
    have hnot : ¬ N < I.length := not_lt.mpr (hlen ▸ le_of_not_gt h)
    simp [if_neg hnot]

lemma levelNorm {d : ℕ} (N : ℕ) (a : ExtTensorAlgebra d) (n : ℕ) :
    (projGt N a).levelNorm n = if N < n then a.levelNorm n else 0 := by
  unfold ExtTensorAlgebra.levelNorm
  rw [projGt.levelNormSq]
  split_ifs <;> simp

end projGt

end SignatureVolatility
