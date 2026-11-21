module

public import SignatureVolatility.ExtTensorAlgebra.ConcatAssoc
public import SignatureVolatility.ExtTensorAlgebra.ExtTensorAlgebra


@[expose] public section

noncomputable section

open Finset

namespace SignatureVolatility

namespace ExtTensorAlgebra

/-- Tensor exponential of a pure level-1 element `v ∈ ℝ^d`. -/
def tensorExp {d : ℕ} (v : Fin d → ℝ) : ExtTensorAlgebra d :=
  ⟨fun I => (I.map v).prod / (I.length.factorial : ℝ)⟩

@[simp] lemma tensorExp_coeff_nil {d : ℕ} (v : Fin d → ℝ) :
    (tensorExp v).coeff [] = 1 := by
  simp [tensorExp]

lemma tensorExp_coeff_singleton {d : ℕ} (v : Fin d → ℝ) (i : Fin d) :
    (tensorExp v).coeff [i] = v i := by
  simp [tensorExp]

lemma concat_tensorExp_zero_left {d : ℕ} (a : ExtTensorAlgebra d) :
    tensorExp (fun _ : Fin d => (0 : ℝ)) ⊗ₜ a = a := by
  ext I
  simp only [concat, tensorExp]
  rw [sum_eq_single 0]
  · simp
  · intro k hk hk0
    have hkle : k ≤ I.length := Nat.lt_succ_iff.mp (mem_range.mp hk)
    have hne : I.take k ≠ [] := by
      intro h
      have := congrArg List.length h
      simp [List.length_take_of_le hkle] at this
      exact hk0 this
    cases h : I.take k with
    | nil => exact (hne h).elim
    | cons _ _ => simp
  · intro hneg
    exact (hneg (by simp)).elim

/-- Folded tensor product of level-1 exponentials along a chain of increments. -/
def foldTensorExp {d : ℕ} : List (Fin d → ℝ) → ExtTensorAlgebra d
  | [] => tensorExp 0
  | v :: vs => tensorExp v ⊗ₜ foldTensorExp vs

lemma foldTensorExp_coeff_nil {d : ℕ} (vs : List (Fin d → ℝ)) :
    (foldTensorExp vs).coeff [] = 1 := by
  induction vs with
  | nil => simp [foldTensorExp, tensorExp]
  | cons v vs ih =>
    simp [foldTensorExp, concat, tensorExp, ih]

lemma foldTensorExp_append {d : ℕ} (us vs : List (Fin d → ℝ)) :
    foldTensorExp (us ++ vs) = foldTensorExp us ⊗ₜ foldTensorExp vs := by
  induction us with
  | nil =>
    simp only [List.nil_append, foldTensorExp]
    exact (concat_tensorExp_zero_left _).symm
  | cons u us ih =>
    simp only [List.cons_append, foldTensorExp, ih, ← concat_assoc]

lemma foldTensorExp_level1_sum {d : ℕ} (vs : List (Fin d → ℝ)) (i : Fin d) :
    (foldTensorExp vs).coeff [i] = (vs.map (fun v => v i)).sum := by
  induction vs with
  | nil => simp [foldTensorExp, tensorExp]
  | cons v vs ih =>
    simp only [foldTensorExp, List.map_cons, List.sum_cons, concat]
    simp only [List.length_singleton]
    rw [sum_range_succ, sum_range_one]
    simp [tensorExp, ih, foldTensorExp_coeff_nil]
    ring

end ExtTensorAlgebra

end SignatureVolatility
