module

public import SignatureVolatility.DualPairing
public import SignatureVolatility.NormWDual
public import SignatureVolatility.NormW
public import SignatureVolatility.MemTwDual
public import SignatureVolatility.MemTw
public import SignatureVolatility.ExtTensorAlgebra.LevelInner
public import SignatureVolatility.ExtTensorAlgebra.LevelNorm
public import SignatureVolatility.Preliminaries


@[expose] public section

noncomputable section

namespace SignatureVolatility

theorem dualPairing_le_normWDual_mul_normW {d : ℕ} (w : Weight)
    {ℓ a : ExtTensorAlgebra d} (hℓ : MemTwDual w ℓ) (ha : MemTw w a) :
    Summable (fun n : ℕ => |ℓ.levelInner a n|) ∧
      |dualPairing ℓ a| ≤ normWDual w ℓ * normW w a := by
  have hpoint : ∀ n : ℕ, |ℓ.levelInner a n| ≤ normWDual w ℓ * (w n * a.levelNorm n) := by
    intro n
    have hw : 0 < w n := w.pos n
    have hbound : ℓ.levelNorm n ≤ normWDual w ℓ * w n :=
      (div_le_iff₀ hw).mp (normWDual.levelNorm_div_le w hℓ n)
    calc
      |ℓ.levelInner a n| ≤ ℓ.levelNorm n * a.levelNorm n := ExtTensorAlgebra.levelInner.abs_le ℓ a n
      _ ≤ (normWDual w ℓ * w n) * a.levelNorm n :=
        mul_le_mul_of_nonneg_right hbound (ExtTensorAlgebra.levelNorm.nonneg a n)
      _ = normWDual w ℓ * (w n * a.levelNorm n) := by ring
  have hdom : Summable (fun n : ℕ => normWDual w ℓ * (w n * a.levelNorm n)) :=
    ha.mul_left (normWDual w ℓ)
  have habs : Summable (fun n : ℕ => |ℓ.levelInner a n|) :=
    Summable.of_nonneg_of_le (fun _ => abs_nonneg _) hpoint hdom
  refine ⟨habs, ?_⟩
  calc
    |dualPairing ℓ a| ≤ ∑' n : ℕ, |ℓ.levelInner a n| := abs_tsum_le_of_summable_abs habs
    _ ≤ ∑' n : ℕ, normWDual w ℓ * (w n * a.levelNorm n) := habs.tsum_le_tsum hpoint hdom
    _ = normWDual w ℓ * normW w a := tsum_mul_left

end SignatureVolatility
