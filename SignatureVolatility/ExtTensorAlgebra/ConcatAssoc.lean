module

public import SignatureVolatility.ExtTensorAlgebra.Concat


@[expose] public section

open Finset

namespace SignatureVolatility

namespace ExtTensorAlgebra

lemma sum_triangle_reindex {α : Type*} [AddCommMonoid α] (n : ℕ) (F : ℕ → ℕ → α) :
    ∑ j ∈ range (n + 1), ∑ i ∈ range (j + 1), F i j =
      ∑ i ∈ range (n + 1), ∑ k ∈ range (n - i + 1), F i (i + k) := by
  induction n with
  | zero => simp
  | succ m ih =>
    rw [sum_range_succ]
    have hRHS :
        ∑ i ∈ range (m + 2), ∑ k ∈ range (m + 1 - i + 1), F i (i + k) =
          ∑ i ∈ range (m + 1), ∑ k ∈ range (m - i + 1), F i (i + k) +
            ∑ i ∈ range (m + 1), F i (m + 1) + F (m + 1) (m + 1) := by
      have hs :
          ∑ i ∈ range (m + 2), ∑ k ∈ range (m + 1 - i + 1), F i (i + k) =
            ∑ i ∈ range (m + 1), ∑ k ∈ range (m + 1 - i + 1), F i (i + k) +
              F (m + 1) (m + 1) := by
        rw [sum_range_succ]
        simp
      refine hs.trans ?_
      have hrow :
          ∑ i ∈ range (m + 1), ∑ k ∈ range (m + 1 - i + 1), F i (i + k) =
            ∑ i ∈ range (m + 1), ∑ k ∈ range (m - i + 1), F i (i + k) +
              ∑ i ∈ range (m + 1), F i (m + 1) := by
        rw [← sum_add_distrib]
        refine sum_congr rfl fun i hi => ?_
        have hi' : i ≤ m := Nat.lt_succ_iff.mp (mem_range.mp hi)
        have : m + 1 - i + 1 = m - i + 1 + 1 := by omega
        rw [this, sum_range_succ]
        congr 1
        congr 1
        omega
      rw [hrow]
    rw [hRHS, ih]
    have hrow' :
        ∑ i ∈ range (m + 2), F i (m + 1) =
          ∑ i ∈ range (m + 1), F i (m + 1) + F (m + 1) (m + 1) :=
      sum_range_succ (fun i => F i (m + 1)) (m + 1)
    rw [hrow']
    ac_rfl

/-- Associativity of word-series concatenation. -/
lemma concat_assoc {d : ℕ} (a b c : ExtTensorAlgebra d) :
    (a ⊗ₜ b) ⊗ₜ c = a ⊗ₜ (b ⊗ₜ c) := by
  ext I
  classical
  simp only [concat]
  set n := I.length
  let F : ℕ → ℕ → ℝ := fun i j =>
    a.coeff (I.take i) * b.coeff ((I.drop i).take (j - i)) * c.coeff (I.drop j)
  have hL :
      ∑ p ∈ range (n + 1),
          (∑ q ∈ range ((I.take p).length + 1),
            a.coeff ((I.take p).take q) * b.coeff ((I.take p).drop q)) *
          c.coeff (I.drop p) =
        ∑ j ∈ range (n + 1), ∑ i ∈ range (j + 1), F i j := by
    refine sum_congr rfl fun j hj => ?_
    have hj' : j ≤ n := Nat.lt_succ_iff.mp (mem_range.mp hj)
    have hlen : (I.take j).length = j := List.length_take_of_le hj'
    simp_rw [hlen]
    rw [sum_mul]
    refine sum_congr rfl fun i hi => ?_
    have hi' : i ≤ j := Nat.lt_succ_iff.mp (mem_range.mp hi)
    have ht : (I.take j).take i = I.take i := by
      rw [List.take_take, min_eq_left hi']
    have hd : (I.take j).drop i = (I.drop i).take (j - i) := List.drop_take
    simp only [F, ht, hd, mul_assoc]
  have hR :
      ∑ r ∈ range (n + 1),
          a.coeff (I.take r) *
            ∑ s ∈ range ((I.drop r).length + 1),
              b.coeff ((I.drop r).take s) * c.coeff ((I.drop r).drop s) =
        ∑ i ∈ range (n + 1), ∑ k ∈ range (n - i + 1), F i (i + k) := by
    refine sum_congr rfl fun i hi => ?_
    have hi' : i ≤ n := Nat.lt_succ_iff.mp (mem_range.mp hi)
    have hlen : (I.drop i).length = n - i := by
      simp [n, List.length_drop]
    simp_rw [hlen]
    rw [mul_sum]
    refine sum_congr rfl fun k hk => ?_
    have hdd : (I.drop i).drop k = I.drop (i + k) := by
      rw [List.drop_drop, Nat.add_comm]
    simp only [F, hdd, Nat.add_sub_cancel_left, mul_assoc]
  exact hL.trans ((sum_triangle_reindex n F).trans hR.symm)

end ExtTensorAlgebra

end SignatureVolatility
