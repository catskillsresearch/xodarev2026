module

public import SignatureVolatility.Weight
public import SignatureVolatility.Weight.ConstOne
public import SignatureVolatility.Weight.Geometric


@[expose] public section

namespace SignatureVolatility

structure HypH2 (w : Weight) where
  C_w : ℝ
  one_le_Cw : 1 ≤ C_w
  submult : ∀ m n : ℕ, w (m + n) ≤ C_w * w m * w n
  subfactorial : ∀ R : ℝ, 0 < R → Summable (fun n : ℕ => w n * (R ^ n / (n.factorial : ℝ)))

namespace HypH2

lemma subfactorial_nonneg {w : Weight} (hw : HypH2 w) {R : ℝ} (hR : 0 ≤ R) :
    Summable (fun n : ℕ => w n * (R ^ n / (n.factorial : ℝ))) := by
  rcases hR.eq_or_lt with rfl | hpos
  · refine Summable.of_nonneg_of_le
      (fun n => mul_nonneg (w.pos n).le (div_nonneg (pow_nonneg le_rfl n) (Nat.cast_nonneg _)))
      (fun n => ?_) (hw.subfactorial 1 zero_lt_one)
    refine mul_le_mul_of_nonneg_left ?_ (w.pos n).le
    exact div_le_div_of_nonneg_right (pow_le_pow_left₀ le_rfl zero_le_one n) (Nat.cast_nonneg _)
  · exact hw.subfactorial R hpos

def geometric_admissible (r : ℝ) (hr : 1 ≤ r) : HypH2 (Weight.geometric r hr) where
  C_w := 1
  one_le_Cw := le_rfl
  submult m n := by simp [Weight.geometric, pow_add]
  subfactorial R _ := by
    have hrew : (fun n : ℕ => (Weight.geometric r hr) n * (R ^ n / (n.factorial : ℝ))) =
        fun n : ℕ => (r * R) ^ n / (n.factorial : ℝ) := by
      ext n
      simp [Weight.geometric, mul_pow, mul_div_assoc]
    rw [hrew]
    exact Real.summable_pow_div_factorial (r * R)

def constOne_admissible : HypH2 Weight.constOne where
  C_w := 1
  one_le_Cw := le_rfl
  submult _ _ := by simp [Weight.constOne]
  subfactorial R _ := by
    simpa [Weight.constOne] using Real.summable_pow_div_factorial R

end HypH2

end SignatureVolatility
