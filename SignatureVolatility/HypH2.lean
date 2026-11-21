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

/-- Submultiplicativity implies at-most-geometric growth. -/
lemma le_geometric {w : Weight} (hw : HypH2 w) :
    ∃ r : ℝ, ∀ n, w n ≤ r ^ n := by
  refine ⟨max 1 (hw.C_w * w 1), fun n => ?_⟩
  have hC : 0 ≤ hw.C_w := zero_le_one.trans hw.one_le_Cw
  have hw1 : 0 ≤ w 1 := (w.pos 1).le
  have hr0 : 0 ≤ max 1 (hw.C_w * w 1) := le_max_of_le_left zero_le_one
  induction n with
  | zero =>
    simp [w.w_zero]
  | succ n ih =>
    calc w (n + 1) ≤ hw.C_w * w n * w 1 := by
          simpa [Nat.add_comm n 1] using hw.submult n 1
      _ ≤ hw.C_w * (max 1 (hw.C_w * w 1)) ^ n * w 1 :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left ih hC) hw1
      _ = (hw.C_w * w 1) * (max 1 (hw.C_w * w 1)) ^ n := by ring
      _ ≤ (max 1 (hw.C_w * w 1)) * (max 1 (hw.C_w * w 1)) ^ n :=
          mul_le_mul_of_nonneg_right (le_max_right _ _) (pow_nonneg hr0 _)
      _ = (max 1 (hw.C_w * w 1)) ^ (n + 1) := (pow_succ' _ _).symm

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
