import SignatureVolatility.MemTwDual
import SignatureVolatility.MemL2w
import SignatureVolatility.NormWDual
import SignatureVolatility.Weight
import SignatureVolatility.ExtTensorAlgebra.LevelNorm
import SignatureVolatility.ExtTensorAlgebra.LevelNormSq
import SignatureVolatility.Norm2w


noncomputable section

namespace SignatureVolatility

lemma memTwDual_of_memL2w {d : ℕ} (w : Weight) {ℓ : ExtTensorAlgebra d} (hℓ : MemL2w w ℓ) :
    MemTwDual w ℓ ∧ normWDual w ℓ ≤ norm2w w ℓ := by
  have hle : ∀ n : ℕ, ℓ.levelNorm n / w n ≤ norm2w w ℓ := by
    intro n
    have hsq : (ℓ.levelNorm n / w n) ^ 2 ≤ ∑' k : ℕ, ℓ.levelNormSq k / (w k) ^ 2 := by
      have heq : (ℓ.levelNorm n / w n) ^ 2 = ℓ.levelNormSq n / (w n) ^ 2 := by
        rw [div_pow, ExtTensorAlgebra.levelNorm.sq ℓ]
      rw [heq]
      exact hℓ.le_tsum n fun k _ => div_nonneg (ExtTensorAlgebra.levelNormSq.nonneg ℓ k) (sq_nonneg _)
    have h0 : 0 ≤ ℓ.levelNorm n / w n := div_nonneg (ExtTensorAlgebra.levelNorm.nonneg ℓ n) (w.pos n).le
    calc
      ℓ.levelNorm n / w n = Real.sqrt ((ℓ.levelNorm n / w n) ^ 2) := (Real.sqrt_sq h0).symm
      _ ≤ norm2w w ℓ := Real.sqrt_le_sqrt hsq
  exact ⟨⟨norm2w w ℓ, by rintro _ ⟨n, rfl⟩; exact hle n⟩, ciSup_le hle⟩

end SignatureVolatility
