import SignatureVolatility.ExtTensorAlgebra.LevelNorm
import SignatureVolatility.MemL2wInv
import SignatureVolatility.MemL2wInvOfMemTw
import SignatureVolatility.MemTw
import SignatureVolatility.Norm2wInv
import SignatureVolatility.NormW
import SignatureVolatility.ProjGt
import SignatureVolatility.Weight

noncomputable section

namespace SignatureVolatility

theorem tail_norm2wInv_le_ratio_mul_normW {d : ℕ} (w w' : Weight)
    {b : ExtTensorAlgebra d} (hb : MemTw w' b) (N : ℕ) {ρ : ℝ} (hρ : 0 ≤ ρ)
    (hratio : ∀ n : ℕ, N < n → w n / w' n ≤ ρ) :
    MemL2wInv w (projGt N b) ∧ norm2wInv w (projGt N b) ≤ ρ * normW w' b := by
  have hterm : ∀ n : ℕ, 0 ≤ w n * (projGt N b).levelNorm n :=
    fun n => mul_nonneg (w.pos n).le (ExtTensorAlgebra.levelNorm.nonneg (projGt N b) n)
  have hpoint : ∀ n : ℕ, w n * (projGt N b).levelNorm n ≤ ρ * (w' n * b.levelNorm n) := by
    intro n
    rw [projGt.levelNorm]
    split_ifs with hn
    · have hw' : 0 < w' n := w'.pos n
      have hw_le : w n ≤ ρ * w' n := (div_le_iff₀ hw').mp (hratio n hn)
      calc
        w n * b.levelNorm n ≤ (ρ * w' n) * b.levelNorm n :=
          mul_le_mul_of_nonneg_right hw_le (ExtTensorAlgebra.levelNorm.nonneg b n)
        _ = ρ * (w' n * b.levelNorm n) := by ring
    · rw [mul_zero]
      exact mul_nonneg hρ (mul_nonneg (w'.pos n).le (ExtTensorAlgebra.levelNorm.nonneg b n))
  have hdom : Summable (fun n : ℕ => ρ * (w' n * b.levelNorm n)) := hb.mul_left ρ
  have hmemTw : MemTw w (projGt N b) := Summable.of_nonneg_of_le hterm hpoint hdom
  obtain ⟨hL2, hle⟩ := memL2wInv_of_memTw w hmemTw
  refine ⟨hL2, hle.trans ?_⟩
  calc
    normW w (projGt N b) ≤ ∑' n : ℕ, ρ * (w' n * b.levelNorm n) :=
      hmemTw.tsum_le_tsum hpoint hdom
    _ = ρ * normW w' b := tsum_mul_left

end SignatureVolatility