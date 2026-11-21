module

public import SignatureVolatility.ExtTensorAlgebra.EvalShuffleBasis
public import SignatureVolatility.ExtTensorAlgebra.TensorExp


@[expose] public section

open List

namespace SignatureVolatility

namespace ExtTensorAlgebra

private lemma choose_div_factorial_add (n m : ℕ) :
    (Nat.choose (n + m) n : ℝ) / ((n + m).factorial : ℝ) =
      (1 : ℝ) / ((n.factorial : ℝ) * (m.factorial : ℝ)) := by
  have hn : n ≤ n + m := Nat.le_add_right _ _
  have hf := Nat.choose_mul_factorial_mul_factorial hn
  rw [Nat.add_sub_cancel_left] at hf
  have hn0 : ((n + m).factorial : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  have hden : (n.factorial : ℝ) * (m.factorial : ℝ) ≠ 0 :=
    mul_ne_zero (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _))
      (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _))
  rw [div_eq_div_iff hn0 hden]
  calc
    (Nat.choose (n + m) n : ℝ) * ((n.factorial : ℝ) * (m.factorial : ℝ)) =
        ↑(Nat.choose (n + m) n * n.factorial * m.factorial) := by push_cast; ring
    _ = ↑(n + m).factorial := by exact_mod_cast hf
    _ = (1 : ℝ) * ↑(n + m).factorial := by ring

private lemma shuffleWords_map_prod {d : ℕ} (v : Fin d → ℝ) (I J : Word d) :
    ∀ K ∈ shuffleWords I J, (K.map v).prod = (I.map v).prod * (J.map v).prod := by
  induction I generalizing J with
  | nil =>
    intro K hK
    simp only [shuffleWords, mem_singleton] at hK
    subst hK
    simp
  | cons i I ih =>
    induction J with
    | nil =>
      intro K hK
      simp only [shuffleWords, mem_singleton] at hK
      subst hK
      simp
    | cons j J ihJ =>
      intro K hK
      simp only [shuffleWords, mem_append, mem_map] at hK
      rcases hK with ⟨K', hK', rfl⟩ | ⟨K', hK', rfl⟩
      · have := ih (j :: J) K' hK'
        simp [this]; ring
      · have := ihJ K' hK'
        simp [this]; ring

private lemma shuffleWords_length_eq {d : ℕ} (I J : Word d) :
    ∀ K ∈ shuffleWords I J, K.length = I.length + J.length := by
  induction I generalizing J with
  | nil =>
    intro K hK
    simp only [shuffleWords, mem_singleton] at hK
    subst hK
    simp
  | cons i I ih =>
    induction J with
    | nil =>
      intro K hK
      simp only [shuffleWords, mem_singleton] at hK
      subst hK
      simp
    | cons j J ihJ =>
      intro K hK
      simp only [shuffleWords, mem_append, mem_map] at hK
      rcases hK with ⟨K', hK', rfl⟩ | ⟨K', hK', rfl⟩
      · have := ih (j :: J) K' hK'
        simp [this]; omega
      · have := ihJ K' hK'
        simp [this]; omega

private lemma length_shuffleWords {d : ℕ} :
    ∀ (I J : Word d),
      (shuffleWords I J).length = Nat.choose (I.length + J.length) I.length := by
  intro I
  induction I with
  | nil =>
    intro J
    simp [shuffleWords]
  | cons i I ih =>
    intro J
    induction J with
    | nil =>
      simp [shuffleWords, Nat.choose_self]
    | cons j J ihJ =>
      simp only [shuffleWords, length_append, length_map, length_cons]
      have h1 := ih (j :: J)
      simp only [length_cons] at h1
      rw [h1, ihJ]
      have hL : I.length + (J.length + 1) = I.length + J.length + 1 := by omega
      have hR : (i :: I).length + J.length = I.length + J.length + 1 := by
        simp [length_cons]; omega
      have hK : (i :: I).length = I.length + 1 := by simp [length_cons]
      have hT : I.length + 1 + (J.length + 1) = (I.length + J.length + 1) + 1 := by omega
      rw [hL, hR, hK, hT]
      exact (Nat.choose_succ_succ (I.length + J.length + 1) I.length).symm

/-- Group-like / shuffle identity for pure level-1 exponentials. -/
lemma tensorExp_shuffle {d : ℕ} (v : Fin d → ℝ) (I J : Word d) :
    (tensorExp v).coeff I * (tensorExp v).coeff J =
      evalShuffleBasis I J (tensorExp v) := by
  classical
  simp only [tensorExp, evalShuffleBasis]
  have hprod (K : Word d) (hK : K ∈ shuffleWords I J) :
      (K.map v).prod / (K.length.factorial : ℝ) =
        (I.map v).prod * (J.map v).prod / ((I.length + J.length).factorial : ℝ) := by
    rw [shuffleWords_map_prod v I J K hK, shuffleWords_length_eq I J K hK]
  have hsum :
      ((shuffleWords I J).map fun K =>
          (K.map v).prod / (K.length.factorial : ℝ)).sum =
        (shuffleWords I J).length *
          ((I.map v).prod * (J.map v).prod / ((I.length + J.length).factorial : ℝ)) := by
    have hconst :
        (shuffleWords I J).map (fun K =>
            (K.map v).prod / (K.length.factorial : ℝ)) =
          (shuffleWords I J).map (fun _ =>
            (I.map v).prod * (J.map v).prod / ((I.length + J.length).factorial : ℝ)) :=
      List.map_congr_left fun K hK => hprod K hK
    rw [hconst, List.map_const', List.sum_replicate, nsmul_eq_mul]
  rw [hsum, length_shuffleWords]
  have hk0 : (I.length.factorial : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  have hj0 : (J.length.factorial : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  have hnm0 : ((I.length + J.length).factorial : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  have hfac := choose_div_factorial_add I.length J.length
  calc
    (I.map v).prod / (I.length.factorial : ℝ) * ((J.map v).prod / (J.length.factorial : ℝ)) =
        (I.map v).prod * (J.map v).prod *
          ((1 : ℝ) / ((I.length.factorial : ℝ) * (J.length.factorial : ℝ))) := by
      field_simp [hk0, hj0]
    _ = (I.map v).prod * (J.map v).prod *
          ((Nat.choose (I.length + J.length) I.length : ℝ) /
            ((I.length + J.length).factorial : ℝ)) := by
      rw [← hfac]
    _ = (Nat.choose (I.length + J.length) I.length : ℝ) *
          ((I.map v).prod * (J.map v).prod / ((I.length + J.length).factorial : ℝ)) := by
      field_simp [hnm0]

end ExtTensorAlgebra

end SignatureVolatility
