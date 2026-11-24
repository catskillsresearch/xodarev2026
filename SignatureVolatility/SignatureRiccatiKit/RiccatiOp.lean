module

public import SignatureVolatility.RiccatiOpBounded

@[expose] public section

noncomputable section

namespace SignatureVolatility

/-!
# The global Riccati operator `ℛ` (paper Definition 18)

`riccatiOp u` is the coefficientwise-exact version of `riccatiOpBounded`: the shuffle
square at output word `K` is truncated at `|K|`, which loses nothing because a shuffle of
words of lengths `m, n` only has words of length `m + n`.  On the finitely supported core
`𝒟_fin` it agrees with `riccatiOpBounded N` for every support bound `N`.
-/

namespace ExtTensorAlgebra

lemma length_of_mem_shuffleWords {d : ℕ} :
    ∀ (I J : Word d) {L : Word d}, L ∈ shuffleWords I J → L.length = I.length + J.length
  | [], J, L, h => by simp [shuffleWords] at h; simp [h]
  | i :: I, [], L, h => by simp [shuffleWords] at h; simp [h]
  | i :: I, j :: J, L, h => by
    rw [shuffleWords] at h
    rcases List.mem_append.1 h with h | h
    · obtain ⟨L', hL', rfl⟩ := List.mem_map.1 h
      have := length_of_mem_shuffleWords I (j :: J) hL'
      simp [this]; omega
    · obtain ⟨L', hL', rfl⟩ := List.mem_map.1 h
      have := length_of_mem_shuffleWords (i :: I) J hL'
      simp [this]; omega
termination_by I J => I.length + J.length

lemma shuffleBasis_coeff_eq_zero {d : ℕ} {I J K : Word d}
    (h : K.length ≠ I.length + J.length) : (shuffleBasis I J).coeff K = 0 := by
  unfold shuffleBasis
  simp only
  apply List.sum_eq_zero
  intro x hx
  obtain ⟨L, hL, rfl⟩ := List.mem_map.1 hx
  have := length_of_mem_shuffleWords I J hL
  rw [ite_eq_right_iff]
  rintro rfl
  exact (h this).elim

lemma coeff_finset_sum {d : ℕ} {ι : Type*} (s : Finset ι) (f : ι → ExtTensorAlgebra d)
    (K : Word d) : (∑ i ∈ s, f i).coeff K = ∑ i ∈ s, (f i).coeff K := by
  classical
  induction s using Finset.induction_on with
  | empty => rfl
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, ← ih]; rfl

end ExtTensorAlgebra

open ExtTensorAlgebra

/-- Paper Definition 18: the global Riccati vector field on `T_w`. -/
def riccatiOp {d : ℕ} (u : ExtTensorAlgebra (d + 1)) : ExtTensorAlgebra (d + 1) :=
  ⟨fun K => (rightShift 0 u + stratonovichHalfLaplacian u).coeff K +
    (1 / 2 : ℝ) * ∑ i : Fin d,
      (shuffleFinite (rightShift i.succ u) (rightShift i.succ u) K.length).coeff K⟩

/-- Support-truncation independence of `shuffleFinite` at a fixed output word. -/
lemma shuffleFinite_coeff_eq_min {d : ℕ} (a b : ExtTensorAlgebra (d + 1)) (c N : ℕ) (hc : c ≤ N)
    (K : Word (d + 1)) (ha : ∀ I : Word (d + 1), c < I.length → a.coeff I = 0)
    (hb : ∀ I : Word (d + 1), c < I.length → b.coeff I = 0) :
    (shuffleFinite a b N).coeff K = (shuffleFinite a b c).coeff K := by
  unfold shuffleFinite
  simp only
  have hsub : Finset.range (c + 1) ⊆ Finset.range (N + 1) :=
    Finset.range_subset_range.2 (by omega)
  rw [← Finset.sum_subset hsub]
  · refine Finset.sum_congr rfl fun m _ => ?_
    symm
    apply Finset.sum_subset hsub
    intro n _ hn
    simp only [Finset.mem_range, not_lt] at hn
    apply Finset.sum_eq_zero; intro I _
    apply Finset.sum_eq_zero; intro J hJ
    rw [hb J (by rw [wordsOfLength.mem.1 hJ]; omega)]; ring
  · intro m _ hm
    simp only [Finset.mem_range, not_lt] at hm
    apply Finset.sum_eq_zero; intro n _
    apply Finset.sum_eq_zero; intro I hI
    apply Finset.sum_eq_zero; intro J _
    rw [ha I (by rw [wordsOfLength.mem.1 hI]; omega)]; ring

/-- At output word `K`, truncating the shuffle at `|K|` loses nothing. -/
lemma shuffleFinite_coeff_eq_length {d : ℕ} (a b : ExtTensorAlgebra (d + 1)) (N : ℕ)
    (K : Word (d + 1)) (hK : K.length ≤ N) :
    (shuffleFinite a b N).coeff K = (shuffleFinite a b K.length).coeff K := by
  unfold shuffleFinite
  simp only
  have hsub : Finset.range (K.length + 1) ⊆ Finset.range (N + 1) :=
    Finset.range_subset_range.2 (by omega)
  rw [← Finset.sum_subset hsub]
  · refine Finset.sum_congr rfl fun m _ => ?_
    symm
    apply Finset.sum_subset hsub
    intro n _ hn
    simp only [Finset.mem_range, not_lt] at hn
    apply Finset.sum_eq_zero; intro I _
    apply Finset.sum_eq_zero; intro J hJ
    rw [shuffleBasis_coeff_eq_zero (by rw [wordsOfLength.mem.1 hJ]; omega)]; ring
  · intro m _ hm
    simp only [Finset.mem_range, not_lt] at hm
    apply Finset.sum_eq_zero; intro n _
    apply Finset.sum_eq_zero; intro I hI
    apply Finset.sum_eq_zero; intro J _
    rw [shuffleBasis_coeff_eq_zero (by rw [wordsOfLength.mem.1 hI]; omega)]; ring

/-- `ℛ` extends the bounded operator from `𝒟_fin`: for `u` supported in depth `≤ N`,
`riccatiOp u` and `riccatiOpBounded N u` have the same coefficients. -/
theorem riccatiOp_eq_bounded {d : ℕ} (N : ℕ) (u : ExtTensorAlgebra (d + 1))
    (hu : ∀ I : Word (d + 1), N < I.length → u.coeff I = 0) (K : Word (d + 1)) :
    (riccatiOp u).coeff K = (riccatiOpBounded N u).coeff K := by
  have hs : ∀ i : Fin d, ∀ I : Word (d + 1), N < I.length →
      (rightShift i.succ u).coeff I = 0 := fun i I hI => hu _ (by simp; omega)
  have hi : ∀ i : Fin d, (shuffleFinite (rightShift i.succ u) (rightShift i.succ u)
      K.length).coeff K =
      (shuffleFinite (rightShift i.succ u) (rightShift i.succ u) N).coeff K := by
    intro i
    rcases le_total K.length N with h | h
    · exact (shuffleFinite_coeff_eq_length _ _ N K h).symm
    · exact shuffleFinite_coeff_eq_min _ _ N K.length h K (hs i) (hs i)
  simp only [riccatiOp, riccatiOpBounded, hi]
  show _ = (rightShift 0 u + stratonovichHalfLaplacian u).coeff K +
    (1 / 2 : ℝ) * (∑ i : Fin d, shuffleFinite (rightShift i.succ u) (rightShift i.succ u) N).coeff K
  rw [coeff_finset_sum]

end SignatureVolatility
