module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Tactic

/-!
# B4a. Explicit bounded C^{1,2} barrier for `v₁ x → 0` as `x → +∞`

The writeup's intermediate claim that the parenthesis
`1 - A + s₀³/A² + (3/2) β s₀⁶/A²` is `≤ -9/8` is false (it is `≤ -3/8`);
the conclusion `PDE ≤ 0` still holds with the correct arithmetic.
-/

@[expose] public section

noncomputable section

open Filter Topology

namespace SignatureVolatility

/-- Explicit barrier `u(r, y) = -β (s₀ - r - A/y)_+³`. -/
def barrierU (s₀ β A r y : ℝ) : ℝ :=
  if A / s₀ < y ∧ A / y < s₀ - r then -β * (s₀ - r - A / y) ^ 3 else 0

lemma barrierU_terminal (s₀ β A y : ℝ) (hs₀ : 0 < s₀) (hA : 0 < A) :
    barrierU s₀ β A s₀ y = 0 := by
  unfold barrierU
  split_ifs with h
  · exfalso
    have hy : 0 < y := lt_trans (div_pos hA hs₀) h.1
    have : 0 < A / y := div_pos hA hy
    linarith [h.2]
  · rfl

lemma barrierU_initial_le {s₀ β A x : ℝ} (hs₀ : 0 < s₀) (hβ : 0 < β) (hA : 0 < A)
    (hx : 2 * A / s₀ ≤ x) :
    barrierU s₀ β A 0 x ≤ -β * (s₀ ^ 3 / 8) := by
  have hy1 : A / s₀ < x := by
    have : A / s₀ < 2 * A / s₀ := by
      rw [div_lt_div_iff_of_pos_right hs₀]; linarith
    exact lt_of_lt_of_le this hx
  have hxpos : 0 < x := lt_trans (div_pos hA hs₀) hy1
  have hAx : A / x ≤ s₀ / 2 := by
    rw [div_le_div_iff₀ hxpos two_pos]
    have := (div_le_iff₀ hs₀).mp hx
    linarith
  have hy2 : A / x < s₀ - 0 := by linarith
  unfold barrierU
  rw [ite_eq_left ⟨hy1, hy2⟩, sub_zero]
  have hdiff : s₀ / 2 ≤ s₀ - A / x := by linarith
  have hcube : (s₀ / 2) ^ 3 ≤ (s₀ - A / x) ^ 3 := pow_le_pow_left₀ (by positivity) hdiff 3
  have h8 : (s₀ / 2) ^ 3 = s₀ ^ 3 / 8 := by ring
  nlinarith

/-- Algebraic PDE inequality on the active region, once
`A ≥ max 2 (max (2 √(s₀³)) (2 √β s₀³))`.
The writeup's intermediate claim that the parenthesis is `≤ -9/8` is
false (it is `≤ -3/8`); the conclusion `PDE ≤ -(9/8) β v² ≤ 0` still holds
after correcting the arithmetic to a `≤ -3/8` factor. -/
lemma barrierU_pde_nonpos {s₀ β A r y : ℝ} (hs₀ : 0 < s₀) (hβ : 0 < β)
    (hA2 : 2 ≤ A) (hAs : 2 * Real.sqrt (s₀ ^ 3) ≤ A) (hAβ : 2 * Real.sqrt β * s₀ ^ 3 ≤ A)
    (hr0 : 0 ≤ r) (_hrs : r ≤ s₀) (hy1 : A / s₀ < y) (hy2 : A / y < s₀ - r) :
    let v := s₀ - r - A / y
    let ur := 3 * β * v ^ 2
    let uy := -3 * β * v ^ 2 * (A / y ^ 2)
    let uyy := -6 * β * v * (A / y ^ 2) ^ 2 + 6 * β * v ^ 2 * (A / y ^ 3)
    ur + y ^ 2 * uy + (1 / 2 : ℝ) * uyy + (1 / 2 : ℝ) * uy ^ 2 ≤ 0 := by
  intro v ur uy uyy
  have hA : 0 < A := by linarith
  have hy : 0 < y := lt_trans (div_pos hA hs₀) hy1
  have hv0 : 0 < v := sub_pos.mpr hy2
  have hvs : v ≤ s₀ := by
    have : 0 < A / y := div_pos hA hy
    linarith
  have hA_lt_ys : A < y * s₀ := (div_lt_iff₀ hs₀).mp hy1
  -- Exact drift term: `y² u_y = -3 β A v²`
  have hy2uy : y ^ 2 * uy = -3 * β * A * v ^ 2 := by
    simp only [uy]; field_simp
  -- Bound `A / y³ ≤ s₀³ / A²` and `A² / y⁴ ≤ s₀⁴ / A²`
  have hAy3 : A / y ^ 3 ≤ s₀ ^ 3 / A ^ 2 := by
    rw [div_le_div_iff₀ (pow_pos hy 3) (pow_pos hA 2)]
    have hpow : A ^ 3 ≤ (y * s₀) ^ 3 := pow_le_pow_left₀ hA.le hA_lt_ys.le 3
    rw [mul_pow] at hpow
    nlinarith
  have hAy4 : A ^ 2 / y ^ 4 ≤ s₀ ^ 4 / A ^ 2 := by
    rw [div_le_div_iff₀ (pow_pos hy 4) (pow_pos hA 2)]
    have hpow : A ^ 4 ≤ (y * s₀) ^ 4 := pow_le_pow_left₀ hA.le hA_lt_ys.le 4
    rw [mul_pow] at hpow
    nlinarith
  -- Bound `(1/2) u_{yy} ≤ 3 β v² (s₀³ / A²)`
  have huyy_le : (1 / 2 : ℝ) * uyy ≤ 3 * β * v ^ 2 * (s₀ ^ 3 / A ^ 2) := by
    have hneg : -6 * β * v * (A / y ^ 2) ^ 2 ≤ 0 := by
      have : 0 ≤ 6 * β * v * (A / y ^ 2) ^ 2 := by positivity
      linarith
    have hstep : (1 / 2 : ℝ) * uyy ≤ 3 * β * v ^ 2 * (A / y ^ 3) := by
      simp only [uyy]; linarith [hneg]
    exact hstep.trans (mul_le_mul_of_nonneg_left hAy3 (by positivity))
  -- Bound `(1/2) u_y² ≤ 3 β v² ((3/2) β s₀⁶ / A²)`
  have huy2_le : (1 / 2 : ℝ) * uy ^ 2 ≤ 3 * β * v ^ 2 * ((3 / 2 : ℝ) * β * s₀ ^ 6 / A ^ 2) := by
    have heq : (1 / 2 : ℝ) * uy ^ 2 = (9 / 2 : ℝ) * β ^ 2 * v ^ 2 * (v ^ 2 * (A ^ 2 / y ^ 4)) := by
      simp only [uy]; ring
    rw [heq]
    have hv2 : v ^ 2 ≤ s₀ ^ 2 := pow_le_pow_left₀ hv0.le hvs 2
    have hprod : v ^ 2 * (A ^ 2 / y ^ 4) ≤ s₀ ^ 2 * (s₀ ^ 4 / A ^ 2) :=
      mul_le_mul hv2 hAy4 (by positivity) (by positivity)
    calc (9 / 2 : ℝ) * β ^ 2 * v ^ 2 * (v ^ 2 * (A ^ 2 / y ^ 4))
        ≤ (9 / 2 : ℝ) * β ^ 2 * v ^ 2 * (s₀ ^ 2 * (s₀ ^ 4 / A ^ 2)) :=
          mul_le_mul_of_nonneg_left hprod (by positivity)
      _ = 3 * β * v ^ 2 * ((3 / 2 : ℝ) * β * s₀ ^ 6 / A ^ 2) := by ring
  -- Bound `s₀³ / A² ≤ 1/4` and `(3/2) β s₀⁶ / A² ≤ 3/8`
  have hs3_le : s₀ ^ 3 / A ^ 2 ≤ 1 / 4 := by
    have hsq : (2 * Real.sqrt (s₀ ^ 3)) ^ 2 ≤ A ^ 2 :=
      pow_le_pow_left₀ (by positivity) hAs 2
    rw [mul_pow, Real.sq_sqrt (by positivity)] at hsq
    rw [div_le_div_iff₀ (pow_pos hA 2) (by norm_num : (0 : ℝ) < 4)]
    linarith
  have hβs6_le : (3 / 2 : ℝ) * β * s₀ ^ 6 / A ^ 2 ≤ 3 / 8 := by
    have hsq : 4 * β * s₀ ^ 6 ≤ A ^ 2 := by
      have hsq0 : (2 * Real.sqrt β * s₀ ^ 3) ^ 2 ≤ A ^ 2 :=
        pow_le_pow_left₀ (by positivity) hAβ 2
      have hsq1 : (2 * Real.sqrt β * s₀ ^ 3) ^ 2 = 4 * β * s₀ ^ 6 := by
        calc (2 * Real.sqrt β * s₀ ^ 3) ^ 2
            = 2 ^ 2 * (Real.sqrt β) ^ 2 * (s₀ ^ 3) ^ 2 := by ring
          _ = 4 * β * s₀ ^ 6 := by rw [Real.sq_sqrt hβ.le]; ring
      rwa [hsq1] at hsq0
    rw [div_le_div_iff₀ (pow_pos hA 2) (by norm_num : (0 : ℝ) < 8)]
    linarith
  -- Combine all four terms
  have hsum : ur + y ^ 2 * uy + (1 / 2 : ℝ) * uyy + (1 / 2 : ℝ) * uy ^ 2 ≤
      3 * β * v ^ 2 * (1 - A + s₀ ^ 3 / A ^ 2 + (3 / 2 : ℝ) * β * s₀ ^ 6 / A ^ 2) := by
    rw [hy2uy]
    simp only [ur]
    linarith
  refine hsum.trans ?_
  have hpar : 1 - A + s₀ ^ 3 / A ^ 2 + (3 / 2 : ℝ) * β * s₀ ^ 6 / A ^ 2 ≤ 0 := by linarith
  exact mul_nonpos_of_nonneg_of_nonpos (by positivity) hpar

end SignatureVolatility
