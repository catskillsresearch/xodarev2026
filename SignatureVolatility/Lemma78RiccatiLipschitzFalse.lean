module

public import SignatureVolatility.Lemma77ShuffleEstimateFalse

@[expose] public section

namespace SignatureVolatility

/-!
# Counterexample to the paper's Lemma 78

**Lemma 78** (paper): *`ℛ` is locally Lipschitz on bounded subsets of `T_w`.* For the H2 weight
`w ≡ 1` and `d ≥ 1` this fails: `u_k = e_{ℓ^{k+1}}` (with `ℓ` a space letter) has `‖u_k‖_w = 1`, but
the coefficient of `ℛ(u_k)` at `ℓ^{2k}` is `½ binom(2k, k) ≥ k` (`not_lemma78_local_lipschitz`).
The shuffle count and weighted-norm lemmas come from `Lemma77ShuffleEstimateFalse`.
-/

open ExtTensorAlgebra

/-! ## Lemma 78 is false -/

lemma riccatiOp_zero_coeff {d : ℕ} (K : Word (d + 1)) : (riccatiOp (0 : ExtTensorAlgebra (d + 1))).coeff K = 0 := by
  have hz : ∀ I : Word (d + 1), (0 : ExtTensorAlgebra (d + 1)).coeff I = 0 := fun _ => rfl
  have hadd : ∀ (a b : ExtTensorAlgebra (d + 1)) (I : Word (d + 1)),
      (a + b).coeff I = a.coeff I + b.coeff I := fun _ _ _ => rfl
  simp [riccatiOp, rightShift, stratonovichHalfLaplacian, shuffleFinite, hz, hadd]

lemma rightShift_basis_replicate {d : ℕ} (k : ℕ) (j : Fin (d + 1)) (ℓ : Fin (d + 1)) (I : Word (d + 1)) :
    (rightShift j (basisWord (List.replicate (k + 1) ℓ))).coeff I =
      if j = ℓ ∧ I = List.replicate k ℓ then 1 else 0 := by
  simp only [rightShift, basisWord]
  congr 1
  apply propext
  rw [List.replicate_succ']
  constructor
  · intro h
    obtain ⟨h1, h2⟩ := List.append_inj' h rfl
    exact ⟨List.singleton_inj.1 h2, h1⟩
  · rintro ⟨rfl, rfl⟩; rfl

lemma riccatiOp_basis_replicate_coeff {d : ℕ} {k : ℕ} (hk : 1 ≤ k) (ℓ : Fin (d + 2))
    (hℓ : (0 : Fin (d + 1)).succ = ℓ) :
    (riccatiOp (basisWord (List.replicate (k + 1) ℓ))).coeff (List.replicate (2 * k) ℓ) =
      (1 / 2 : ℝ) * ((2 * k).choose k : ℝ) := by
  have hℓ0 : ℓ ≠ 0 := hℓ ▸ Fin.succ_ne_zero _
  have hlin : (rightShift 0 (basisWord (List.replicate (k + 1) ℓ)) +
      stratonovichHalfLaplacian (basisWord (List.replicate (k + 1) ℓ))).coeff
        (List.replicate (2 * k) ℓ) = 0 := by
    have h1 : List.replicate (2 * k) ℓ ++ [0] ≠ List.replicate (k + 1) ℓ := fun h => by
      have : (0 : Fin (d + 2)) ∈ List.replicate (k + 1) ℓ := h ▸ by simp
      exact hℓ0 (List.eq_of_mem_replicate this).symm
    have h2 : ∀ i : Fin (d + 1), List.replicate (2 * k) ℓ ++ [i.succ, i.succ] ≠
        List.replicate (k + 1) ℓ := fun i h => by
      have := congrArg List.length h
      simp at this; omega
    change (basisWord (List.replicate (k + 1) ℓ)).coeff (List.replicate (2 * k) ℓ ++ [0]) +
      (1 / 2 : ℝ) * ∑ i : Fin (d + 1), (basisWord (List.replicate (k + 1) ℓ)).coeff
        (List.replicate (2 * k) ℓ ++ [i.succ, i.succ]) = 0
    simp only [basisWord, h1, h2, ite_false, Finset.sum_const_zero, mul_zero, add_zero]
  have hsh : ∀ i : Fin (d + 1),
      (shuffleFinite (rightShift i.succ (basisWord (List.replicate (k + 1) ℓ)))
        (rightShift i.succ (basisWord (List.replicate (k + 1) ℓ)))
        (List.replicate (2 * k) ℓ).length).coeff (List.replicate (2 * k) ℓ) =
        if i = 0 then ((2 * k).choose k : ℝ) else 0 := by
    intro i
    simp only [shuffleFinite, rightShift_basis_replicate]
    by_cases hi : i = 0
    · subst hi
      simp only [hℓ, true_and, ite_true, List.length_replicate]
      have hR : ∀ m : ℕ, ∀ I ∈ wordsOfLength (d + 2) m, m ≠ k → I ≠ List.replicate k ℓ :=
        fun m I hI hm e => hm (by rw [← wordsOfLength.mem.1 hI, e]; simp)
      rw [Finset.sum_eq_single k, Finset.sum_eq_single k]
      · rw [Finset.sum_eq_single (List.replicate k ℓ), Finset.sum_eq_single (List.replicate k ℓ)]
        · simp only [ite_true, one_mul]
          rw [show List.replicate (2 * k) ℓ = List.replicate (k + k) ℓ by rw [two_mul],
            shuffleBasis_replicate_coeff, two_mul]
        · intro J _ hJ; simp only [hJ, ite_false, mul_zero, zero_mul]
        · intro h; exact (h (wordsOfLength.mem.2 (by simp))).elim
        · intro J _ hJ; simp only [hJ, ite_false, zero_mul, Finset.sum_const_zero]
        · intro h; exact (h (wordsOfLength.mem.2 (by simp))).elim
      · intro n _ hn
        refine Finset.sum_eq_zero fun I _ => Finset.sum_eq_zero fun J hJ => ?_
        simp only [hR n J hJ hn, ite_false, mul_zero, zero_mul]
      · intro h; exact (h (Finset.mem_range.2 (by omega))).elim
      · intro m _ hm
        refine Finset.sum_eq_zero fun n _ => Finset.sum_eq_zero fun I hI => ?_
        refine Finset.sum_eq_zero fun J _ => ?_
        simp only [hR m I hI hm, ite_false, zero_mul]
      · intro h; exact (h (Finset.mem_range.2 (by omega))).elim
    · have : i.succ ≠ ℓ := fun e => hi (Fin.succ_inj.1 (e.trans hℓ.symm))
      simp only [this, false_and, ite_false, zero_mul, mul_zero, Finset.sum_const_zero, hi]
  change (rightShift 0 (basisWord (List.replicate (k + 1) ℓ)) +
      stratonovichHalfLaplacian (basisWord (List.replicate (k + 1) ℓ))).coeff
        (List.replicate (2 * k) ℓ) + (1 / 2 : ℝ) * ∑ i : Fin (d + 1),
      (shuffleFinite (rightShift i.succ (basisWord (List.replicate (k + 1) ℓ)))
        (rightShift i.succ (basisWord (List.replicate (k + 1) ℓ)))
        (List.replicate (2 * k) ℓ).length).coeff (List.replicate (2 * k) ℓ) = _
  rw [hlin, zero_add, Finset.sum_congr rfl fun i _ => hsh i,
    Finset.sum_ite_eq' Finset.univ (0 : Fin (d + 1))]
  simp

/-- **Paper Lemma 78 is false**: for the H2 weight `w ≡ 1` and at least one space dimension, the
Riccati operator `ℛ` is not locally Lipschitz on bounded subsets of `T_w` (it is not even bounded
on the unit ball). -/
theorem not_lemma78_local_lipschitz {d : ℕ} :
    ¬ ∀ ρ : ℝ, 0 < ρ → ∃ L : ℝ, ∀ u v : ExtTensorAlgebra (d + 2),
      MemTw Weight.constOne u → MemTw Weight.constOne v →
      normW Weight.constOne u ≤ ρ → normW Weight.constOne v ≤ ρ →
      MemTw Weight.constOne (riccatiOp u - riccatiOp v) ∧
        normW Weight.constOne (riccatiOp u - riccatiOp v) ≤ L * normW Weight.constOne (u - v) := by
  intro h
  obtain ⟨L, hL⟩ := h 1 one_pos
  set ℓ : Fin (d + 2) := (0 : Fin (d + 1)).succ
  set k : ℕ := ⌈L⌉₊ + 1
  have hk : 1 ≤ k := Nat.le_add_left 1 _
  set u := basisWord (List.replicate (k + 1) ℓ)
  have hnu : normW Weight.constOne u = 1 := by rw [normW_basisWord]; rfl
  have hn0 : normW Weight.constOne (0 : ExtTensorAlgebra (d + 2)) = 0 := by
    unfold normW
    rw [show (fun n => Weight.constOne n * (0 : ExtTensorAlgebra (d + 2)).levelNorm n) =
      fun _ => (0 : ℝ) from funext fun n => by rw [levelNorm_eq_zero_of fun _ _ => rfl, mul_zero],
      tsum_zero]
  obtain ⟨hmem, hle⟩ := hL u 0 (memTw_basisWord _ _) (memTw_of_single_level _ 0 fun _ _ => rfl)
    hnu.le (by rw [hn0]; exact zero_le_one)
  rw [sub_zero, hnu, mul_one] at hle
  have hlow := mul_abs_coeff_le_normW Weight.constOne hmem (List.replicate (2 * k) ℓ)
  have hc : (riccatiOp u - riccatiOp 0).coeff (List.replicate (2 * k) ℓ) =
      (1 / 2 : ℝ) * ((2 * k).choose k : ℝ) := by
    change (riccatiOp u).coeff _ - (riccatiOp 0).coeff _ = _
    rw [riccatiOp_zero_coeff, sub_zero, riccatiOp_basis_replicate_coeff hk ℓ rfl]
  rw [hc, show Weight.constOne (List.replicate (2 * k) ℓ).length = 1 from rfl, one_mul] at hlow
  have hch : (2 * k : ℕ) ≤ (2 * k).choose k := by
    have := Nat.choose_le_centralBinom 1 k
    rw [Nat.choose_one_right] at this
    simpa [Nat.centralBinom] using this
  have hch' : (2 * k : ℝ) ≤ ((2 * k).choose k : ℝ) := by exact_mod_cast hch
  have hceil : L ≤ (⌈L⌉₊ : ℝ) := Nat.le_ceil L
  have hkR : (k : ℝ) = ⌈L⌉₊ + 1 := by simp [k]
  rw [abs_of_nonneg (by positivity)] at hlow
  nlinarith

end SignatureVolatility
