module

public import SignatureVolatility.DualPairing
public import SignatureVolatility.ExtTensorAlgebra.TensorExpLevelNorm


@[expose] public section

namespace SignatureVolatility

namespace ExtTensorAlgebra

/-!
# Lipschitz bounds for the level components of the tensor exponential

For `x, y ∈ ℝ^d` with Euclidean norms at most `R`,
`‖x^{⊗n} - y^{⊗n}‖ ≤ n ‖x - y‖ R^{n-1}` (`sqrt_sum_prod_sub_sq_le`), hence
`|⟨ℓ_n, exp⊗ x⟩ - ⟨ℓ_n, exp⊗ y⟩| ≤ ‖ℓ_n‖ · n ‖x - y‖ R^{n-1} / n!`
(`abs_levelInner_tensorExp_sub_le`).
-/

private lemma sqrt_pow_eq {a : ℝ} (ha : 0 ≤ a) (n : ℕ) : Real.sqrt (a ^ n) = Real.sqrt a ^ n := by
  rw [show a ^ n = (Real.sqrt a ^ n) ^ 2 by rw [← pow_mul, mul_comm, pow_mul, Real.sq_sqrt ha],
    Real.sqrt_sq (by positivity)]

/-- `‖x^{⊗n} - y^{⊗n}‖₂ ≤ n ‖x - y‖₂ R^{n-1}` on words of length `n`. -/
lemma sqrt_sum_prod_sub_sq_le {d : ℕ} (x y : Fin d → ℝ) {R : ℝ}
    (hx : Real.sqrt (∑ i, x i ^ 2) ≤ R) (hy : Real.sqrt (∑ i, y i ^ 2) ≤ R) :
    ∀ n : ℕ, Real.sqrt (∑ I ∈ wordsOfLength d n, ((I.map x).prod - (I.map y).prod) ^ 2) ≤
      n * Real.sqrt (∑ i, (x i - y i) ^ 2) * R ^ (n - 1)
  | 0 => by simp [wordsOfLength]
  | n + 1 => by
    have hR0 : 0 ≤ R := (Real.sqrt_nonneg _).trans hx
    have ih := sqrt_sum_prod_sub_sq_le x y hx hy n
    have hsplit : ∑ I ∈ wordsOfLength d (n + 1), ((I.map x).prod - (I.map y).prod) ^ 2 =
        ∑ p ∈ (Finset.univ : Finset (Fin d)) ×ˢ wordsOfLength d n,
          (x p.1 * ((p.2.map x).prod - (p.2.map y).prod) +
            (x p.1 - y p.1) * (p.2.map y).prod) ^ 2 := by
      rw [wordsOfLength.succ, Finset.sum_product]
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun J _ => ?_
      simp only [List.map_cons, List.prod_cons]
      ring
    have hf : ∑ p ∈ (Finset.univ : Finset (Fin d)) ×ˢ wordsOfLength d n,
        (x p.1 * ((p.2.map x).prod - (p.2.map y).prod)) ^ 2 =
        (∑ i, x i ^ 2) * ∑ I ∈ wordsOfLength d n, ((I.map x).prod - (I.map y).prod) ^ 2 := by
      rw [Finset.sum_product, Finset.sum_mul]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun J _ => ?_
      ring
    have hg : ∑ p ∈ (Finset.univ : Finset (Fin d)) ×ˢ wordsOfLength d n,
        ((x p.1 - y p.1) * (p.2.map y).prod) ^ 2 =
        (∑ i, (x i - y i) ^ 2) * (∑ i, y i ^ 2) ^ n := by
      rw [Finset.sum_product, ← sum_wordsOfLength_prod_sq, Finset.sum_mul]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun J _ => ?_
      ring
    have hmink := sqrt_sum_add_sq_le ((Finset.univ : Finset (Fin d)) ×ˢ wordsOfLength d n)
      (fun p => x p.1 * ((p.2.map x).prod - (p.2.map y).prod))
      (fun p => (x p.1 - y p.1) * (p.2.map y).prod)
    rw [← hsplit, hf, hg, Real.sqrt_mul (Finset.sum_nonneg fun _ _ => sq_nonneg _),
      Real.sqrt_mul (Finset.sum_nonneg fun _ _ => sq_nonneg _),
      sqrt_pow_eq (Finset.sum_nonneg fun _ _ => sq_nonneg _)] at hmink
    have hNd : 0 ≤ Real.sqrt (∑ i, (x i - y i) ^ 2) := Real.sqrt_nonneg _
    have hDn := Real.sqrt_nonneg
      (∑ I ∈ wordsOfLength d n, ((I.map x).prod - (I.map y).prod) ^ 2)
    have h1 : Real.sqrt (∑ i, x i ^ 2) *
        Real.sqrt (∑ I ∈ wordsOfLength d n, ((I.map x).prod - (I.map y).prod) ^ 2) ≤
        n * Real.sqrt (∑ i, (x i - y i) ^ 2) * R ^ n := by
      calc _ ≤ R * (n * Real.sqrt (∑ i, (x i - y i) ^ 2) * R ^ (n - 1)) :=
            mul_le_mul hx ih hDn hR0
        _ = n * Real.sqrt (∑ i, (x i - y i) ^ 2) * R ^ n := by
            rcases n with _ | m
            · simp
            · simp only [Nat.add_sub_cancel, pow_succ]; push_cast; ring
    have h2 : Real.sqrt (∑ i, (x i - y i) ^ 2) * Real.sqrt (∑ i, y i ^ 2) ^ n ≤
        Real.sqrt (∑ i, (x i - y i) ^ 2) * R ^ n :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (Real.sqrt_nonneg _) hy n) hNd
    calc _ ≤ _ := hmink
      _ ≤ n * Real.sqrt (∑ i, (x i - y i) ^ 2) * R ^ n +
          Real.sqrt (∑ i, (x i - y i) ^ 2) * R ^ n := add_le_add h1 h2
      _ = ((n + 1 : ℕ) : ℝ) * Real.sqrt (∑ i, (x i - y i) ^ 2) * R ^ (n + 1 - 1) := by
          rw [Nat.add_sub_cancel]; push_cast; ring

lemma levelInner_sub {d : ℕ} (ℓ a b : ExtTensorAlgebra d) (n : ℕ) :
    levelInner ℓ a n - levelInner ℓ b n = levelInner ℓ (a - b) n := by
  unfold levelInner
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun I _ => ?_
  change _ = ℓ.coeff I * (a.coeff I - b.coeff I)
  ring

lemma levelNorm_tensorExp_sub {d : ℕ} (x y : Fin d → ℝ) (n : ℕ) :
    levelNorm (tensorExp x - tensorExp y) n =
      Real.sqrt (∑ I ∈ wordsOfLength d n, ((I.map x).prod - (I.map y).prod) ^ 2) /
        (n.factorial : ℝ) := by
  have hf : (0 : ℝ) < n.factorial := by exact_mod_cast n.factorial_pos
  unfold levelNorm levelNormSq
  rw [eq_div_iff hf.ne', ← Real.sqrt_sq hf.le, ← Real.sqrt_mul (Finset.sum_nonneg fun _ _ =>
    sq_nonneg _), Finset.sum_mul]
  congr 1
  refine Finset.sum_congr rfl fun I hI => ?_
  have hlen : I.length = n := wordsOfLength.mem.mp hI
  change ((I.map x).prod / (I.length.factorial : ℝ) - (I.map y).prod /
    (I.length.factorial : ℝ)) ^ 2 * _ = _
  rw [hlen]
  field_simp

/-- **Level-wise Lipschitz bound** for the pairing with the tensor exponential. -/
lemma abs_levelInner_tensorExp_sub_le {d : ℕ} (ℓ : ExtTensorAlgebra d) (x y : Fin d → ℝ)
    {R : ℝ} (hx : Real.sqrt (∑ i, x i ^ 2) ≤ R) (hy : Real.sqrt (∑ i, y i ^ 2) ≤ R) (n : ℕ) :
    |levelInner ℓ (tensorExp x) n - levelInner ℓ (tensorExp y) n| ≤
      levelNorm ℓ n * (n * Real.sqrt (∑ i, (x i - y i) ^ 2) * R ^ (n - 1) /
        (n.factorial : ℝ)) := by
  rw [levelInner_sub]
  refine (levelInner.abs_le _ _ n).trans (mul_le_mul_of_nonneg_left ?_ (levelNorm.nonneg ℓ n))
  rw [levelNorm_tensorExp_sub]
  exact div_le_div_of_nonneg_right (sqrt_sum_prod_sub_sq_le x y hx hy n) (Nat.cast_nonneg _)

private lemma hasSum_exp_series (x : ℝ) :
    HasSum (fun n : ℕ => x ^ n / (n.factorial : ℝ)) (Real.exp x) := by
  rw [Real.exp_eq_exp_ℝ]
  exact NormedSpace.expSeries_div_hasSum_exp x

/-- **Uniform bound** for `⟨ℓ, exp⊗ x⟩` when `‖ℓ_n‖ ≤ C rⁿ` and `‖x‖ ≤ R`. -/
lemma abs_dualPairing_tensorExp_le {d : ℕ} (ℓ : ExtTensorAlgebra d) {C r R : ℝ}
    (hℓ : ∀ n, levelNorm ℓ n ≤ C * r ^ n) (x : Fin d → ℝ)
    (hx : Real.sqrt (∑ i, x i ^ 2) ≤ R) :
    |dualPairing ℓ (tensorExp x)| ≤ C * Real.exp (r * R) := by
  have hR0 : 0 ≤ R := (Real.sqrt_nonneg _).trans hx
  rw [← Real.norm_eq_abs]
  refine tsum_of_norm_bounded ((hasSum_exp_series (r * R)).mul_left C) fun n => ?_
  rw [Real.norm_eq_abs]
  refine (levelInner.abs_le _ _ n).trans ?_
  rw [tensorExp_levelNorm]
  have hf : (0 : ℝ) < n.factorial := by exact_mod_cast n.factorial_pos
  calc levelNorm ℓ n * (Real.sqrt (∑ i, x i ^ 2) ^ n / (n.factorial : ℝ))
      ≤ (C * r ^ n) * (R ^ n / (n.factorial : ℝ)) :=
        mul_le_mul (hℓ n) (div_le_div_of_nonneg_right
          (pow_le_pow_left₀ (Real.sqrt_nonneg _) hx n) hf.le) (by positivity)
          ((levelNorm.nonneg ℓ n).trans (hℓ n))
    _ = C * ((r * R) ^ n / (n.factorial : ℝ)) := by rw [mul_pow]; ring

/-- **Lipschitz bound** for `x ↦ ⟨ℓ, exp⊗ x⟩` on the ball of radius `R`, when
`‖ℓ_n‖ ≤ C rⁿ`. -/
lemma abs_dualPairing_tensorExp_sub_le {d : ℕ} (ℓ : ExtTensorAlgebra d) {C r R : ℝ}
    (hℓ : ∀ n, levelNorm ℓ n ≤ C * r ^ n) (x y : Fin d → ℝ)
    (hx : Real.sqrt (∑ i, x i ^ 2) ≤ R) (hy : Real.sqrt (∑ i, y i ^ 2) ≤ R) :
    |dualPairing ℓ (tensorExp x) - dualPairing ℓ (tensorExp y)| ≤
      C * r * Real.sqrt (∑ i, (x i - y i) ^ 2) * Real.exp (r * R) := by
  have hR0 : 0 ≤ R := (Real.sqrt_nonneg _).trans hx
  have hC : 0 ≤ C := by
    have := (levelNorm.nonneg ℓ 0).trans (hℓ 0)
    simpa using this
  set N := Real.sqrt (∑ i, (x i - y i) ^ 2) with hN
  have hN0 : 0 ≤ N := Real.sqrt_nonneg _
  have hsumm : ∀ z : Fin d → ℝ, Real.sqrt (∑ i, z i ^ 2) ≤ R →
      Summable fun n => levelInner ℓ (tensorExp z) n := by
    intro z hz
    refine Summable.of_norm_bounded ((hasSum_exp_series (r * R)).mul_left C).summable
      fun n => ?_
    rw [Real.norm_eq_abs]
    refine (levelInner.abs_le _ _ n).trans ?_
    rw [tensorExp_levelNorm]
    have hf : (0 : ℝ) < n.factorial := by exact_mod_cast n.factorial_pos
    calc levelNorm ℓ n * (Real.sqrt (∑ i, z i ^ 2) ^ n / (n.factorial : ℝ))
        ≤ (C * r ^ n) * (R ^ n / (n.factorial : ℝ)) :=
          mul_le_mul (hℓ n) (div_le_div_of_nonneg_right
            (pow_le_pow_left₀ (Real.sqrt_nonneg _) hz n) hf.le) (by positivity)
            ((levelNorm.nonneg ℓ n).trans (hℓ n))
      _ = C * ((r * R) ^ n / (n.factorial : ℝ)) := by rw [mul_pow]; ring
  -- the majorant `v n = C N rⁿ n R^{n-1} / n!` sums to `C r N exp(r R)`
  set v : ℕ → ℝ := fun n => C * (r ^ n * (n * N * R ^ (n - 1) / (n.factorial : ℝ))) with hv
  have hvsum : HasSum v (C * r * N * Real.exp (r * R)) := by
    rw [← hasSum_nat_add_iff' 1]
    have hv0 : ∑ i ∈ Finset.range 1, v i = 0 := by simp [hv]
    rw [hv0, sub_zero]
    have hshift : (fun n => v (n + 1)) =
        fun n => C * r * N * ((r * R) ^ n / (n.factorial : ℝ)) := by
      funext n
      simp only [hv, Nat.add_sub_cancel, Nat.factorial_succ]
      have hf : (0 : ℝ) < n.factorial := by exact_mod_cast n.factorial_pos
      push_cast
      field_simp
      ring
    rw [hshift]
    exact (hasSum_exp_series (r * R)).mul_left (C * r * N)
  unfold dualPairing
  rw [← (hsumm x hx).tsum_sub (hsumm y hy), ← Real.norm_eq_abs]
  refine tsum_of_norm_bounded hvsum fun n => ?_
  rw [Real.norm_eq_abs]
  refine (abs_levelInner_tensorExp_sub_le ℓ x y hx hy n).trans ?_
  have hf : (0 : ℝ) < n.factorial := by exact_mod_cast n.factorial_pos
  calc _ ≤ (C * r ^ n) * (n * N * R ^ (n - 1) / (n.factorial : ℝ)) :=
        mul_le_mul_of_nonneg_right (hℓ n) (by positivity)
    _ = v n := by simp only [hv]; ring

end ExtTensorAlgebra

end SignatureVolatility
