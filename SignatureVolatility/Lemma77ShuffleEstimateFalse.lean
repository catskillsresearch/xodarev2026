module

public import SignatureVolatility.NormW
public import SignatureVolatility.MemTw
public import SignatureVolatility.HypH2
public import SignatureVolatility.SignatureRiccatiKit.RiccatiOp

@[expose] public section


namespace SignatureVolatility

/-!
# Counterexamples to the paper's Lemmas 77 and 78

**Lemma 77** (paper, Appendix): *assume H2; there is `C` with `‖a ⧢ b‖_w ≤ C ‖a‖_w ‖b‖_w` on `T_w`.*
This is false for **every** weight (Definition 9: `w(0) = 1`, `w` increasing), so in particular for
every H2 weight. For a single letter `ℓ`, `ℓ^{k} ⧢ ℓ = (k + 1) ℓ^{k+1}`, so
`‖ℓ^k ⧢ ℓ‖_w = (k + 1) w(k + 1) ≥ (k + 1) w(k)`, while `‖ℓ^k‖_w ‖ℓ‖_w = w(k) w(1)`
(`not_lemma77_shuffle_estimate`). The paper's proof claims the binomial factor `≤ 2ⁿ` is absorbed by
"an equivalent weight"; that requires `2ⁿ w(n)`, which is not equivalent to `w`.

**Lemma 78** (paper): *`ℛ` is locally Lipschitz on bounded subsets of `T_w`.* For the H2 weight
`w ≡ 1` and `d ≥ 1` this fails: `u_k = e_{ℓ^{k+1}}` (with `ℓ` a space letter) has `‖u_k‖_w = 1`, but
the coefficient of `ℛ(u_k)` at `ℓ^{2k}` is `½ binom(2k, k) ≥ k` (`not_lemma78_local_lipschitz`).

The basic count is `count_replicate_shuffleWords`: `ℓ^{a+b}` occurs `binom(a+b, a)` times in
`shuffleWords ℓ^a ℓ^b`.
-/

open ExtTensorAlgebra

/-! ## Shuffles of one-letter words -/

lemma count_replicate_shuffleWords {d : ℕ} (l : Fin d) :
    ∀ a b : ℕ, (shuffleWords (List.replicate a l) (List.replicate b l)).count
      (List.replicate (a + b) l) = (a + b).choose a
  | 0, b => by simp [shuffleWords]
  | a + 1, 0 => by simp [List.replicate_succ, shuffleWords]
  | a + 1, b + 1 => by
    have h1 : (shuffleWords (List.replicate a l) (l :: List.replicate b l)).count
        (List.replicate (a + (b + 1)) l) = (a + (b + 1)).choose a :=
      count_replicate_shuffleWords l a (b + 1)
    have h2 : (shuffleWords (l :: List.replicate a l) (List.replicate b l)).count
        (List.replicate (a + (b + 1)) l) = (a + (b + 1)).choose (a + 1) := by
      rw [show a + (b + 1) = a + 1 + b by omega]
      exact count_replicate_shuffleWords l (a + 1) b
    have h3 : ∀ L : List (Word d), (L.map fun x => l :: x).count (l :: List.replicate (a + (b + 1)) l) =
        L.count (List.replicate (a + (b + 1)) l) := fun L =>
      List.count_map_of_injective L (fun x => l :: x) List.cons_injective _
    rw [show a + 1 + (b + 1) = (a + (b + 1)) + 1 by omega, List.replicate_succ,
      List.replicate_succ, List.replicate_succ, shuffleWords, List.count_append, h3, h3, h1, h2,
      Nat.choose_succ_succ']
  termination_by a b => a + b

lemma sum_map_ite_eq_count {d : ℕ} (K : Word d) :
    ∀ Ls : List (Word d), (Ls.map fun L => if K = L then (1 : ℝ) else 0).sum = (Ls.count K : ℝ)
  | [] => by simp
  | L :: Ls => by
    rw [List.map_cons, List.sum_cons, sum_map_ite_eq_count K Ls, List.count_cons]
    by_cases h : K = L
    · subst h
      simp only [ite_true, beq_self_eq_true]
      push_cast; ring
    · have h' : (L == K) = false := beq_false_of_ne (Ne.symm h)
      simp only [h, ite_false, h']
      push_cast; ring

lemma shuffleBasis_coeff_eq_count {d : ℕ} (I J K : Word d) :
    (shuffleBasis I J).coeff K = ((shuffleWords I J).count K : ℝ) :=
  sum_map_ite_eq_count K _

lemma shuffleBasis_replicate_coeff {d : ℕ} (l : Fin d) (a b : ℕ) :
    (shuffleBasis (List.replicate a l) (List.replicate b l)).coeff (List.replicate (a + b) l) =
      ((a + b).choose a : ℝ) := by
  rw [shuffleBasis_coeff_eq_count, count_replicate_shuffleWords]

/-! ## Weighted norms -/

lemma abs_coeff_le_levelNorm_length {d : ℕ} (x : ExtTensorAlgebra d) (K : Word d) :
    |x.coeff K| ≤ x.levelNorm K.length := by
  unfold levelNorm levelNormSq
  rw [← Real.sqrt_sq_eq_abs]
  exact Real.sqrt_le_sqrt (Finset.single_le_sum (f := fun I => x.coeff I ^ 2)
    (fun _ _ => sq_nonneg _) (wordsOfLength.mem.2 rfl))

lemma mul_abs_coeff_le_normW {d : ℕ} (w : Weight) {x : ExtTensorAlgebra d} (hx : MemTw w x)
    (K : Word d) : w K.length * |x.coeff K| ≤ normW w x :=
  (mul_le_mul_of_nonneg_left (abs_coeff_le_levelNorm_length x K) (w.pos _).le).trans
    (hx.le_tsum K.length fun n _ => mul_nonneg (w.pos n).le (levelNorm.nonneg x n))

lemma levelNorm_eq_zero_of {d : ℕ} {x : ExtTensorAlgebra d} {n : ℕ}
    (h : ∀ I : Word d, I.length = n → x.coeff I = 0) : x.levelNorm n = 0 := by
  unfold levelNorm levelNormSq
  rw [Finset.sum_eq_zero fun I hI => by rw [h I (wordsOfLength.mem.1 hI)]; ring, Real.sqrt_zero]

lemma memTw_of_single_level {d : ℕ} (w : Weight) {x : ExtTensorAlgebra d} (m : ℕ)
    (h : ∀ I : Word d, I.length ≠ m → x.coeff I = 0) : MemTw w x := by
  refine summable_of_ne_finset_zero (s := {m}) fun n hn => ?_
  rw [levelNorm_eq_zero_of fun I hI => h I (by rw [hI]; simpa using hn), mul_zero]

lemma normW_basisWord {d : ℕ} (w : Weight) (I : Word d) : normW w (basisWord I) = w I.length := by
  unfold normW
  rw [tsum_eq_single I.length fun n hn => by
    rw [levelNorm_eq_zero_of fun J hJ => by
      have : J ≠ I := fun e => hn (by rw [← hJ, e])
      simp [basisWord, this], mul_zero]]
  have : (basisWord I).levelNorm I.length = 1 := by
    unfold levelNorm levelNormSq
    rw [Finset.sum_eq_single I (fun J _ hJ => by simp [basisWord, hJ])
      (fun h => (h (wordsOfLength.mem.2 rfl)).elim)]
    simp [basisWord]
  rw [this, mul_one]

lemma memTw_basisWord {d : ℕ} (w : Weight) (I : Word d) : MemTw w (basisWord I) :=
  memTw_of_single_level w I.length fun J hJ => by
    have : J ≠ I := fun e => hJ (by rw [e])
    simp [basisWord, this]

/-! ## Lemma 77 is false -/

/-- **Paper Lemma 77 is false** for every weight, in particular for every H2 weight: already on
basis words there is no constant `C` with `‖e_I ⧢ e_J‖_w ≤ C ‖e_I‖_w ‖e_J‖_w`. -/
theorem not_lemma77_shuffle_estimate {d : ℕ} (w : Weight) (l : Fin d) :
    ¬ ∃ C : ℝ, ∀ I J : Word d,
      normW w (shuffleBasis I J) ≤ C * normW w (basisWord I) * normW w (basisWord J) := by
  rintro ⟨C, hC⟩
  set k : ℕ := ⌈|C| * w 1⌉₊
  have h := hC (List.replicate k l) [l]
  rw [normW_basisWord, normW_basisWord, List.length_replicate] at h
  have hmem : MemTw w (shuffleBasis (List.replicate k l) [l]) :=
    memTw_of_single_level w (k + 1) fun I hI => shuffleBasis_coeff_eq_zero (by simpa using hI)
  have hlow := mul_abs_coeff_le_normW w hmem (List.replicate (k + 1) l)
  rw [show [l] = List.replicate 1 l from rfl, shuffleBasis_replicate_coeff,
    List.length_replicate, Nat.choose_succ_self_right] at hlow
  simp only [List.length_singleton] at h
  have hk1 : w k ≤ w (k + 1) := w.mono (Nat.le_succ k)
  have hw1 := w.pos 1
  have hwk := w.pos k
  have hceil : |C| * w 1 ≤ k := Nat.le_ceil _
  have hCabs : C * w k * w 1 ≤ |C| * w (k + 1) * w 1 := by
    have : C * w k ≤ |C| * w (k + 1) :=
      (mul_le_mul_of_nonneg_right (le_abs_self C) hwk.le).trans
        (mul_le_mul_of_nonneg_left hk1 (abs_nonneg C))
    exact mul_le_mul_of_nonneg_right this hw1.le
  have hpos := w.pos (k + 1)
  have habs : |((k + 1 : ℕ) : ℝ)| = (k : ℝ) + 1 := by push_cast; exact abs_of_pos (by positivity)
  rw [habs] at hlow
  have e : List.replicate 1 l = [l] := rfl
  rw [e] at hlow
  have hprod := mul_le_mul_of_nonneg_left hceil hpos.le
  nlinarith

/-- Lemma 77 fails for every H2 weight (the hypothesis of the paper's statement). -/
theorem not_lemma77_of_hypH2 {d : ℕ} (w : Weight) (_hw : HypH2 w) (l : Fin d) :
    ¬ ∃ C : ℝ, ∀ I J : Word d,
      normW w (shuffleBasis I J) ≤ C * normW w (basisWord I) * normW w (basisWord J) :=
  not_lemma77_shuffle_estimate w l

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
