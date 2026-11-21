import SignatureVolatility.ExtTensorAlgebra.ExtTensorAlgebra
import SignatureVolatility.ExtTensorAlgebra.BasisWord
import SignatureVolatility.Letter
import SignatureVolatility.Word

open scoped BigOperators Classical ENNReal NNReal RealInnerProductSpace
open MeasureTheory Filter Topology Set

noncomputable section

namespace SignatureVolatility

namespace ExtTensorAlgebra

def concat {d : ℕ} (a b : ExtTensorAlgebra d) : ExtTensorAlgebra d :=
  ⟨fun I => ∑ k ∈ Finset.range (I.length + 1), a.coeff (I.take k) * b.coeff (I.drop k)⟩

infixl:70 " ⊗ₜ " => concat

namespace concat

/-- Concatenation acts on canonical basis elements as `e_I ⊗ e_J = e_{IJ}`. -/
lemma of_basisWord {d : ℕ} (I J : Word d) :
    basisWord I ⊗ₜ basisWord J = basisWord (I ++ J) := by
  -- Avoid shadowing the ambient `basisWord` def by the lemma name.
  let e {d : ℕ} (K : Word d) : ExtTensorAlgebra d := basisWord K
  ext L
  change (∑ k ∈ Finset.range (L.length + 1),
      (e I).coeff (L.take k) * (e J).coeff (L.drop k)) =
    (e (I ++ J)).coeff L
  simp only [e, basisWord]
  by_cases hL : L = I ++ J
  · subst hL
    have hmem : I.length ∈ Finset.range ((I ++ J).length + 1) := by
      rw [Finset.mem_range, List.length_append]
      omega
    rw [Finset.sum_eq_single I.length]
    · have htake : (I ++ J).take I.length = I := List.take_left
      have hdrop : (I ++ J).drop I.length = J := List.drop_left
      simp [htake, hdrop]
    · intro k hk hne
      have hkle : k ≤ (I ++ J).length := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
      have htake_ne : (I ++ J).take k ≠ I := by
        intro heq
        have hlen := congrArg List.length heq
        rw [List.length_take_of_le hkle] at hlen
        exact hne hlen
      simp [htake_ne]
    · intro hnot
      exact absurd hmem hnot
  · have hne : (if L = I ++ J then (1 : ℝ) else 0) = 0 := by simp [hL]
    rw [hne]
    refine Finset.sum_eq_zero fun k _ => ?_
    by_cases h1 : L.take k = I
    · have h2 : L.drop k ≠ J := by
        intro h2
        apply hL
        rw [← List.take_append_drop k L, h1, h2]
      simp [h1, h2]
    · simp [h1]

end concat

end ExtTensorAlgebra

end SignatureVolatility
