module

public import SignatureVolatility.ExtTensorAlgebra.TensorExp


@[expose] public section

open Finset

namespace SignatureVolatility

namespace ExtTensorAlgebra

private lemma map_neg_prod {d : ℕ} (v : Fin d → ℝ) (L : List (Fin d)) :
    (L.map (fun i => -v i)).prod = (-1 : ℝ) ^ L.length * (L.map v).prod := by
  induction L with
  | nil => simp
  | cons a as ih =>
    simp [ih, pow_succ]
    ring

private lemma prod_take_mul_prod_drop {d : ℕ} (v : Fin d → ℝ) (I : List (Fin d)) (k : ℕ) :
    ((I.take k).map v).prod * ((I.drop k).map v).prod = (I.map v).prod := by
  conv_rhs => rw [← List.take_append_drop k I, List.map_append, List.prod_append]

/-- Binomial identity: `∑_{k=0}^n choose(n,k) (-1)^{n-k} = 0` for `n > 0`. -/
private lemma sum_choose_signed_eq_zero {n : ℕ} (hn : 0 < n) :
    ∑ k ∈ range (n + 1), (n.choose k : ℝ) * (-1 : ℝ) ^ (n - k) = 0 := by
  have h := add_pow (1 : ℝ) (-1) n
  rw [show (1 + (-1 : ℝ)) = (0 : ℝ) by ring, zero_pow hn.ne'] at h
  refine Eq.trans ?_ h.symm
  refine sum_congr rfl fun k _ => ?_
  ring

private lemma choose_div_factorial {n k : ℕ} (hk : k ≤ n) :
    (n.choose k : ℝ) / (n.factorial : ℝ) =
      (1 : ℝ) / ((k.factorial : ℝ) * ((n - k).factorial : ℝ)) := by
  have hf := Nat.choose_mul_factorial_mul_factorial hk
  have hn0 : (n.factorial : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  have hden : (k.factorial : ℝ) * ((n - k).factorial : ℝ) ≠ 0 :=
    mul_ne_zero (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _))
      (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _))
  rw [div_eq_div_iff hn0 hden]
  -- `div_eq_div_iff`: need `choose * (k!*(n-k)!) = 1 * n!`
  calc
    (n.choose k : ℝ) * ((k.factorial : ℝ) * ((n - k).factorial : ℝ)) =
        ↑(n.choose k * k.factorial * (n - k).factorial) := by push_cast; ring
    _ = ↑n.factorial := by rw [hf]
    _ = (1 : ℝ) * ↑n.factorial := by ring

/-- `∑ (-1)^{n-k}/(k!(n-k)!) = 0` for `n > 0`. -/
private lemma binom_signed_inv_factorial_sum_eq_zero {n : ℕ} (hn : 0 < n) :
    ∑ k ∈ range (n + 1),
        ((-1 : ℝ) ^ (n - k)) / ((k.factorial : ℝ) * ((n - k).factorial : ℝ)) = 0 := by
  have hterm (k : ℕ) (hk : k ≤ n) :
      ((-1 : ℝ) ^ (n - k)) / ((k.factorial : ℝ) * ((n - k).factorial : ℝ)) =
        (n.factorial : ℝ)⁻¹ * ((n.choose k : ℝ) * (-1 : ℝ) ^ (n - k)) := by
    have h := choose_div_factorial hk
    -- 1/(k!(n-k)!) = choose/n!
    have h1 : (1 : ℝ) / ((k.factorial : ℝ) * ((n - k).factorial : ℝ)) =
        (n.choose k : ℝ) / (n.factorial : ℝ) := h.symm
    calc
      ((-1 : ℝ) ^ (n - k)) / ((k.factorial : ℝ) * ((n - k).factorial : ℝ)) =
          ((-1 : ℝ) ^ (n - k)) *
            ((1 : ℝ) / ((k.factorial : ℝ) * ((n - k).factorial : ℝ))) := by
        rw [div_eq_mul_inv, one_div]
      _ = ((-1 : ℝ) ^ (n - k)) * ((n.choose k : ℝ) / (n.factorial : ℝ)) := by rw [h1]
      _ = (n.factorial : ℝ)⁻¹ * ((n.choose k : ℝ) * (-1 : ℝ) ^ (n - k)) := by
        rw [div_eq_mul_inv]; ring
  calc
    ∑ k ∈ range (n + 1),
          ((-1 : ℝ) ^ (n - k)) / ((k.factorial : ℝ) * ((n - k).factorial : ℝ)) =
        ∑ k ∈ range (n + 1),
          (n.factorial : ℝ)⁻¹ * ((n.choose k : ℝ) * (-1 : ℝ) ^ (n - k)) :=
      sum_congr rfl fun k hk => hterm k (Nat.lt_succ_iff.mp (mem_range.mp hk))
    _ = (n.factorial : ℝ)⁻¹ *
          ∑ k ∈ range (n + 1), (n.choose k : ℝ) * (-1 : ℝ) ^ (n - k) := by
      rw [← mul_sum]
    _ = (n.factorial : ℝ)⁻¹ * 0 := by rw [sum_choose_signed_eq_zero hn]
    _ = 0 := by ring

private lemma tensorExp_neg_summand {d : ℕ} (v : Fin d → ℝ) (I : Word d) (k : ℕ)
    (hk : k ≤ I.length) :
    ((I.take k).map v).prod / ((I.take k).length.factorial : ℝ) *
        (((I.drop k).map (fun i => -v i)).prod / ((I.drop k).length.factorial : ℝ)) =
      (I.map v).prod *
        (((-1 : ℝ) ^ (I.length - k)) /
          ((k.factorial : ℝ) * ((I.length - k).factorial : ℝ))) := by
  have htk : (I.take k).length = k := List.length_take_of_le hk
  have hdk : (I.drop k).length = I.length - k := by simp [List.length_drop]
  rw [htk, hdk, map_neg_prod v (I.drop k), hdk]
  set n := I.length
  set a := ((I.take k).map v).prod
  set b := ((I.drop k).map v).prod
  set s := (-1 : ℝ) ^ (n - k)
  change a / (k.factorial : ℝ) * (s * b / ((n - k).factorial : ℝ)) =
    (I.map v).prod * (s / ((k.factorial : ℝ) * ((n - k).factorial : ℝ)))
  have hab : a * b = (I.map v).prod := prod_take_mul_prod_drop v I k
  have hk0 : (k.factorial : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  have hnk0 : ((n - k).factorial : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  calc
    a / (k.factorial : ℝ) * (s * b / ((n - k).factorial : ℝ)) =
        (a * (s * b)) / ((k.factorial : ℝ) * ((n - k).factorial : ℝ)) := by
      field_simp [hk0, hnk0]
    _ = (s * (a * b)) / ((k.factorial : ℝ) * ((n - k).factorial : ℝ)) := by ring
    _ = (s * (I.map v).prod) / ((k.factorial : ℝ) * ((n - k).factorial : ℝ)) := by
      rw [hab]
    _ = (I.map v).prod * (s / ((k.factorial : ℝ) * ((n - k).factorial : ℝ))) := by
      field_simp [hk0, hnk0]

/-- Pure level-1 exponentials invert: `exp(v) ⊗ exp(-v) = 1`. -/
lemma tensorExp_neg {d : ℕ} (v : Fin d → ℝ) :
    tensorExp v ⊗ₜ tensorExp (-v) = tensorExp 0 := by
  ext I
  classical
  simp only [concat, tensorExp]
  by_cases hI : I = []
  · subst hI
    simp
  · have hn0 : 0 < I.length := List.length_pos_of_ne_nil hI
    change
      ∑ k ∈ range (I.length + 1),
          ((I.take k).map v).prod / ((I.take k).length.factorial : ℝ) *
            (((I.drop k).map (fun i => -v i)).prod /
              ((I.drop k).length.factorial : ℝ)) =
        (I.map (fun _ : Fin d => (0 : ℝ))).prod / (I.length.factorial : ℝ)
    have hrhs : (I.map (fun _ : Fin d => (0 : ℝ))).prod / (I.length.factorial : ℝ) = 0 := by
      obtain ⟨a, as, rfl⟩ := List.exists_cons_of_ne_nil hI
      simp [List.map]
    rw [hrhs]
    calc
      ∑ k ∈ range (I.length + 1),
            ((I.take k).map v).prod / ((I.take k).length.factorial : ℝ) *
              (((I.drop k).map (fun i => -v i)).prod /
                ((I.drop k).length.factorial : ℝ)) =
          ∑ k ∈ range (I.length + 1),
            (I.map v).prod *
              (((-1 : ℝ) ^ (I.length - k)) /
                ((k.factorial : ℝ) * ((I.length - k).factorial : ℝ))) :=
        sum_congr rfl fun k hk =>
          tensorExp_neg_summand v I k (Nat.lt_succ_iff.mp (mem_range.mp hk))
      _ = (I.map v).prod *
            ∑ k ∈ range (I.length + 1),
              ((-1 : ℝ) ^ (I.length - k)) /
                ((k.factorial : ℝ) * ((I.length - k).factorial : ℝ)) := by
        rw [← mul_sum]
      _ = (I.map v).prod * 0 := by rw [binom_signed_inv_factorial_sum_eq_zero hn0]
      _ = 0 := by ring

lemma tensorExp_mul_inv {d : ℕ} (v : Fin d → ℝ) :
    tensorExp (-v) ⊗ₜ tensorExp v = tensorExp 0 := by
  simpa [neg_neg] using tensorExp_neg (-v)

end ExtTensorAlgebra

end SignatureVolatility
