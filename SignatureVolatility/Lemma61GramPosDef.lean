import SignatureVolatility.Preliminaries

open scoped RealInnerProductSpace

namespace SignatureVolatility

/-- Gram matrix `c^T G c` is positive when the `v_i` are independent and `c ≠ 0`. -/
theorem lemma_6_1_gram_pos_def {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    {m : ℕ} (v : Fin m → H) (hlind : LinearIndependent ℝ v)
    (c : Fin m → ℝ) (hc : c ≠ 0) :
    0 < ∑ i : Fin m, ∑ j : Fin m, c i * c j * ⟪v i, v j⟫ := by
  have heq : (∑ i : Fin m, ∑ j : Fin m, c i * c j * ⟪v i, v j⟫) =
      ‖∑ i : Fin m, c i • v i‖ ^ 2 := by
    rw [← real_inner_self_eq_norm_sq, sum_inner]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [inner_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [real_inner_smul_left, real_inner_smul_right]
    ring
  rw [heq]
  have hnz : ∑ i : Fin m, c i • v i ≠ 0 := by
    intro hzero
    have hall := Fintype.linearIndependent_iff.mp hlind c hzero
    exact hc (funext hall)
  exact sq_pos_of_pos (norm_pos_iff.mpr hnz)

end SignatureVolatility