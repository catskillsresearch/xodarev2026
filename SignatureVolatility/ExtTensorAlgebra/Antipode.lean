import SignatureVolatility.ExtTensorAlgebra.ExtTensorAlgebra
import SignatureVolatility.ExtTensorAlgebra.BasisWord

noncomputable section

namespace SignatureVolatility

namespace ExtTensorAlgebra

def antipode {d : ℕ} (a : ExtTensorAlgebra d) : ExtTensorAlgebra d :=
  ⟨fun I => (-1 : ℝ) ^ I.length * a.coeff I.reverse⟩

namespace antipode

lemma basisWord {d : ℕ} (I : Word d) :
    antipode (basisWord I) = ((-1 : ℝ) ^ I.length) • basisWord I.reverse := by
  ext J
  simp only [antipode, basisWord]
  change (-1 : ℝ) ^ J.length * (if J.reverse = I then 1 else 0) =
    (-1 : ℝ) ^ I.length * (if J = I.reverse then 1 else 0)
  by_cases h : J = I.reverse
  · subst h
    simp
  · have h' : J.reverse ≠ I := fun hr => h (by rw [← hr, List.reverse_reverse])
    simp [h, h']

lemma involutive {d : ℕ} (a : ExtTensorAlgebra d) :
    antipode (antipode a) = a := by
  ext I
  simp only [antipode, List.length_reverse, List.reverse_reverse]
  rw [← mul_assoc, ← mul_pow]
  norm_num


end antipode

end ExtTensorAlgebra

end SignatureVolatility
