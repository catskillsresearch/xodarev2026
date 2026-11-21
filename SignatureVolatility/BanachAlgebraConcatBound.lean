module

public import SignatureVolatility.MemTw
public import SignatureVolatility.NormW
public import SignatureVolatility.Weight
public import SignatureVolatility.ExtTensorAlgebra.Concat
public import SignatureVolatility.ExtTensorAlgebra.LevelNorm
public import SignatureVolatility.Preliminaries


@[expose] public section

noncomputable section

namespace SignatureVolatility

theorem banach_algebra_concat_bound {d : ℕ} (w : Weight) {C_w : ℝ} (hCw : 1 ≤ C_w)
    (hsub : ∀ m n : ℕ, w (m + n) ≤ C_w * w m * w n)
    {a b : ExtTensorAlgebra d} (ha : MemTw w a) (hb : MemTw w b) :
    MemTw w (a ⊗ₜ b) ∧ normW w (a ⊗ₜ b) ≤ C_w * normW w a * normW w b := by
  have hCw0 : 0 ≤ C_w := zero_le_one.trans hCw
  have hterm_nonneg : ∀ n : ℕ, 0 ≤ w n * (a ⊗ₜ b).levelNorm n :=
    fun n => mul_nonneg (w.pos n).le (ExtTensorAlgebra.levelNorm.nonneg (a ⊗ₜ b) n)
  have hrange : ∀ N : ℕ,
      (∑ n ∈ Finset.range N, w n * (a ⊗ₜ b).levelNorm n) ≤ C_w * normW w a * normW w b := by
    intro N
    calc
      ∑ n ∈ Finset.range N, w n * (a ⊗ₜ b).levelNorm n
          ≤ ∑ n ∈ Finset.range N,
              w n * (∑ k ∈ Finset.range (n + 1), a.levelNorm k * b.levelNorm (n - k)) := by
            refine Finset.sum_le_sum fun n _ => ?_
            exact mul_le_mul_of_nonneg_left (ExtTensorAlgebra.levelNorm.concat_le a b n)
              (w.pos n).le
      _ ≤ ∑ n ∈ Finset.range N,
            ∑ k ∈ Finset.range (n + 1),
              C_w * (w k * a.levelNorm k) * (w (n - k) * b.levelNorm (n - k)) := by
            refine Finset.sum_le_sum fun n _ => ?_
            rw [Finset.mul_sum]
            refine Finset.sum_le_sum fun k hk => ?_
            have hkn : k ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
            have hw_kn : w n ≤ C_w * w k * w (n - k) := by
              have h := hsub k (n - k)
              rwa [Nat.add_sub_of_le hkn] at h
            calc
              w n * (a.levelNorm k * b.levelNorm (n - k))
                  ≤ (C_w * w k * w (n - k)) * (a.levelNorm k * b.levelNorm (n - k)) :=
                    mul_le_mul_of_nonneg_right hw_kn
                      (mul_nonneg (ExtTensorAlgebra.levelNorm.nonneg a k) (ExtTensorAlgebra.levelNorm.nonneg b (n - k)))
              _ = C_w * (w k * a.levelNorm k) * (w (n - k) * b.levelNorm (n - k)) := by ring
      _ = C_w * (∑ n ∈ Finset.range N,
            ∑ k ∈ Finset.range (n + 1),
              (w k * a.levelNorm k) * (w (n - k) * b.levelNorm (n - k))) := by
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl fun n _ => ?_
            rw [Finset.mul_sum]
            exact Finset.sum_congr rfl fun k _ => by ring
      _ ≤ C_w * ((∑ k ∈ Finset.range N, w k * a.levelNorm k) *
            (∑ j ∈ Finset.range N, w j * b.levelNorm j)) := by
            refine mul_le_mul_of_nonneg_left ?_ hCw0
            exact cauchy_range_sum_le N
              (fun k => w k * a.levelNorm k)
              (fun j => w j * b.levelNorm j)
              (fun k => mul_nonneg (w.pos k).le (ExtTensorAlgebra.levelNorm.nonneg a k))
              (fun j => mul_nonneg (w.pos j).le (ExtTensorAlgebra.levelNorm.nonneg b j))
      _ ≤ C_w * (normW w a * normW w b) := by
            refine mul_le_mul_of_nonneg_left ?_ hCw0
            refine mul_le_mul ?_ ?_ ?_ (normW.nonneg w a)
            · exact ha.sum_le_tsum (Finset.range N)
                fun k _ => mul_nonneg (w.pos k).le (ExtTensorAlgebra.levelNorm.nonneg a k)
            · exact hb.sum_le_tsum (Finset.range N)
                fun j _ => mul_nonneg (w.pos j).le (ExtTensorAlgebra.levelNorm.nonneg b j)
            · exact Finset.sum_nonneg
                fun j _ => mul_nonneg (w.pos j).le (ExtTensorAlgebra.levelNorm.nonneg b j)
      _ = C_w * normW w a * normW w b := by ring
  have hsum : Summable (fun n : ℕ => w n * (a ⊗ₜ b).levelNorm n) :=
    summable_of_sum_range_le hterm_nonneg hrange
  exact ⟨hsum, hsum.tsum_le_of_sum_range_le hrange⟩

end SignatureVolatility
