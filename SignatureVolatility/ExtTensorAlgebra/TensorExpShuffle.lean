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

/-! ### Concatenation of group-like elements is group-like -/

/-- Sum of `F` over all deconcatenations `I = I₁ ++ I₂`. -/
private def splitSum {d : ℕ} (F : Word d → Word d → ℝ) (I : Word d) : ℝ :=
  ∑ k ∈ Finset.range (I.length + 1), F (I.take k) (I.drop k)

/-- Sum of `f` over all shuffles of `I` and `J`. -/
private def shuffleSum {d : ℕ} (f : Word d → ℝ) (I J : Word d) : ℝ :=
  ((shuffleWords I J).map f).sum

private lemma splitSum_nil {d : ℕ} (F : Word d → Word d → ℝ) :
    splitSum F [] = F [] [] := by
  simp [splitSum]

private lemma splitSum_cons {d : ℕ} (F : Word d → Word d → ℝ) (i : Fin d) (I : Word d) :
    splitSum F (i :: I) = F [] (i :: I) + splitSum (fun a b => F (i :: a) b) I := by
  simp only [splitSum, length_cons, Finset.sum_range_succ', take_succ_cons, drop_succ_cons,
    take_zero, drop_zero]
  exact add_comm _ _

private lemma splitSum_add {d : ℕ} (F G : Word d → Word d → ℝ) (I : Word d) :
    splitSum (fun a b => F a b + G a b) I = splitSum F I + splitSum G I :=
  Finset.sum_add_distrib

private lemma shuffleSum_nil_left {d : ℕ} (f : Word d → ℝ) (J : Word d) :
    shuffleSum f [] J = f J := by
  simp [shuffleSum, shuffleWords]

private lemma shuffleSum_nil_right {d : ℕ} (f : Word d → ℝ) (I : Word d) :
    shuffleSum f I [] = f I := by
  cases I <;> simp [shuffleSum, shuffleWords]

private lemma shuffleSum_cons_cons {d : ℕ} (f : Word d → ℝ) (i j : Fin d) (I J : Word d) :
    shuffleSum f (i :: I) (j :: J) =
      shuffleSum (fun K => f (i :: K)) I (j :: J) +
        shuffleSum (fun K => f (j :: K)) (i :: I) J := by
  simp [shuffleSum, shuffleWords, Function.comp_def]

private lemma shuffleSum_add {d : ℕ} (f g : Word d → ℝ) (I J : Word d) :
    shuffleSum (fun K => f K + g K) I J = shuffleSum f I J + shuffleSum g I J :=
  List.sum_map_add

private lemma shuffleSum_mul_left {d : ℕ} (c : ℝ) (f : Word d → ℝ) (I J : Word d) :
    shuffleSum (fun K => c * f K) I J = c * shuffleSum f I J :=
  List.sum_map_mul_left _ _ _

private lemma shuffleSum_mul_right {d : ℕ} (c : ℝ) (f : Word d → ℝ) (I J : Word d) :
    shuffleSum (fun K => f K * c) I J = shuffleSum f I J * c :=
  List.sum_map_mul_right _ _ _

/-- Deconcatenation is multiplicative for the shuffle product: splitting a shuffle of
`I` and `J` is the same as shuffling the pieces of a splitting of `I` and of `J`. -/
private lemma shuffleSum_splitSum {d : ℕ} (F : Word d → Word d → ℝ) (I J : Word d) :
    shuffleSum (splitSum F) I J =
      splitSum (fun I₁ I₂ => splitSum (fun J₁ J₂ =>
        shuffleSum (fun K₁ => shuffleSum (F K₁) I₂ J₂) I₁ J₁) J) I := by
  induction I generalizing F J with
  | nil => simp [splitSum_nil, shuffleSum_nil_left]
  | cons i I ih =>
    induction J generalizing F with
    | nil => simp [splitSum_nil, shuffleSum_nil_right]
    | cons j J ihJ =>
      simp only [shuffleSum_cons_cons, splitSum_cons, splitSum_add, shuffleSum_add, ih, ihJ,
        shuffleSum_nil_left, shuffleSum_nil_right]
      ring

/-- Group-like elements (shuffle characters) are closed under concatenation. -/
lemma concat_shuffle {d : ℕ} {A B : ExtTensorAlgebra d}
    (hA : ∀ I J, A.coeff I * A.coeff J = evalShuffleBasis I J A)
    (hB : ∀ I J, B.coeff I * B.coeff J = evalShuffleBasis I J B)
    (I J : Word d) :
    (A ⊗ₜ B).coeff I * (A ⊗ₜ B).coeff J = evalShuffleBasis I J (A ⊗ₜ B) := by
  have hA' : ∀ I J, shuffleSum A.coeff I J = A.coeff I * A.coeff J := fun I J => (hA I J).symm
  have hB' : ∀ I J, shuffleSum B.coeff I J = B.coeff I * B.coeff J := fun I J => (hB I J).symm
  change splitSum (fun a b => A.coeff a * B.coeff b) I *
      splitSum (fun a b => A.coeff a * B.coeff b) J =
    shuffleSum (splitSum fun a b => A.coeff a * B.coeff b) I J
  rw [shuffleSum_splitSum]
  simp only [shuffleSum_mul_left, shuffleSum_mul_right, hA', hB']
  simp only [splitSum, Finset.sum_mul_sum]
  exact Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => by ring

/-- Group-like / shuffle identity for folded products of level-1 exponentials. -/
lemma foldTensorExp_shuffle {d : ℕ} (vs : List (Fin d → ℝ)) (I J : Word d) :
    (foldTensorExp vs).coeff I * (foldTensorExp vs).coeff J =
      evalShuffleBasis I J (foldTensorExp vs) := by
  induction vs generalizing I J with
  | nil => exact tensorExp_shuffle 0 I J
  | cons v vs ih => exact concat_shuffle (tensorExp_shuffle v) ih I J

end ExtTensorAlgebra

end SignatureVolatility
