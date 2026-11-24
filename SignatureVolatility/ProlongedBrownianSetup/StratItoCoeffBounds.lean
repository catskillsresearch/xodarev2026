module

public import SignatureVolatility.ProlongedBrownianSetup.StratonovichItoConversion

@[expose] public section

open MeasureTheory

namespace SignatureVolatility

/-!
# Size bounds for the Stratonovich–Itô conversion coefficients

`0 ≤ a_{K,J} ≤ 2^{|K|}` and `a_{K,J} ≠ 0 → |K| ≤ 2 |J|`: each contraction removes one letter and
the contracted pairs are disjoint. Also the first-letter recursion of the contraction list and
the list form `S^K = Σ_{(c,J) ∈ contractions K} c · I^J` of the conversion.
-/

variable {d : ℕ}

/-- First-letter recursion for the contraction list. -/
lemma contractions_cons (j : Fin (d + 1)) (K : Word (d + 1)) :
    contractions (j :: K) = (contractions K).map (fun p => (p.1, j :: p.2)) ++
      (if K.head? = some j ∧ (j : ℕ) ≠ 0 then
        (contractions K.tail).map (fun p => (p.1 / 2, (0 : Fin (d + 1)) :: p.2)) else []) := by
  match K with
  | [] => simp [contractions]
  | j' :: K =>
    rw [contractions]
    have : (j = j' ∧ (j : ℕ) ≠ 0) ↔ ((j' :: K).head? = some j ∧ (j : ℕ) ≠ 0) := by
      simp [eq_comm]
    simp only [this, List.tail_cons]

/-- A time letter never contracts. -/
lemma contractions_cons_zero (K : Word (d + 1)) :
    contractions ((0 : Fin (d + 1)) :: K) =
      (contractions K).map (fun p => (p.1, (0 : Fin (d + 1)) :: p.2)) := by
  rw [contractions_cons]
  simp

lemma contractions_eq_cons (I : Word (d + 1)) :
    contractions I = (1, I) :: (contractions I).tail := by
  induction I with
  | nil => rfl
  | cons j K ih =>
    rw [contractions_cons, ih]
    simp

lemma contractions_props : ∀ (n : ℕ) (I : Word (d + 1)), I.length ≤ n →
    (∀ p ∈ contractions I, 0 < p.1 ∧ p.1 ≤ 1 ∧ p.2.length ≤ I.length ∧
        I.length ≤ 2 * p.2.length) ∧
      (∀ p ∈ (contractions I).tail, p.2.length < I.length) ∧
      (contractions I).length ≤ 2 ^ I.length
  | 0, I, h => by
    have : I = [] := List.eq_nil_of_length_eq_zero (by omega)
    subst this
    simp [contractions]
  | n + 1, [], _ => by simp [contractions]
  | n + 1, j :: K, h => by
    have hK : K.length ≤ n := by simp at h; omega
    have hKt : K.tail.length ≤ n := by simp; omega
    obtain ⟨A1, B1, C1⟩ := contractions_props n K hK
    obtain ⟨A2, -, C2⟩ := contractions_props n K.tail hKt
    have hKtl : K.tail.length + 1 = K.length ∨ K = [] := by
      cases K <;> simp
    refine ⟨?_, ?_, ?_⟩
    · intro p hp
      rw [contractions_cons, List.mem_append] at hp
      rcases hp with hp | hp
      · obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hp
        obtain ⟨a, b, c, e⟩ := A1 q hq
        simp only [List.length_cons]
        exact ⟨a, b, by omega, by omega⟩
      · split_ifs at hp with hc
        · obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hp
          obtain ⟨a, b, c, e⟩ := A2 q hq
          have hne : K ≠ [] := by rintro rfl; simp at hc
          have hl : K.tail.length + 1 = K.length := by
            rcases hKtl with h | h
            · exact h
            · exact absurd h hne
          simp only [List.length_cons]
          refine ⟨by positivity, by linarith, by omega, by omega⟩
        · simp at hp
    · intro p hp
      rw [contractions_cons, contractions_eq_cons K] at hp
      simp only [List.map_cons, List.cons_append, List.tail_cons, List.mem_append] at hp
      rcases hp with hp | hp
      · obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hp
        have := B1 q hq
        simp only [List.length_cons]
        omega
      · split_ifs at hp with hc
        · obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hp
          obtain ⟨-, -, c, -⟩ := A2 q hq
          have hne : K ≠ [] := by rintro rfl; simp at hc
          have hl : K.tail.length + 1 = K.length := by
            rcases hKtl with h | h
            · exact h
            · exact absurd h hne
          simp only [List.length_cons]
          omega
        · simp at hp
    · rw [contractions_cons, List.length_append, List.length_map]
      have h2 : (2 : ℕ) ^ K.tail.length ≤ 2 ^ K.length :=
        Nat.pow_le_pow_right (by norm_num) (by simp)
      split_ifs
      · simp only [List.length_map, List.length_cons, pow_succ]
        omega
      · simp only [List.length_nil, List.length_cons, pow_succ]
        omega

lemma mem_contractions {I : Word (d + 1)} {p : ℝ × Word (d + 1)} (hp : p ∈ contractions I) :
    0 < p.1 ∧ p.1 ≤ 1 ∧ p.2.length ≤ I.length ∧ I.length ≤ 2 * p.2.length :=
  (contractions_props I.length I le_rfl).1 p hp

lemma length_lt_of_mem_tail_contractions {I : Word (d + 1)} {p : ℝ × Word (d + 1)}
    (hp : p ∈ (contractions I).tail) : p.2.length < I.length :=
  (contractions_props I.length I le_rfl).2.1 p hp

lemma length_contractions_le (I : Word (d + 1)) : (contractions I).length ≤ 2 ^ I.length :=
  (contractions_props I.length I le_rfl).2.2

lemma stratItoCoeff_nonneg (I J : Word (d + 1)) : 0 ≤ stratItoCoeff I J := by
  unfold stratItoCoeff
  refine List.sum_nonneg fun x hx => ?_
  obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hx
  exact (mem_contractions (List.mem_of_mem_tail (List.mem_filter.1 hp).1)).1.le

lemma stratItoCoeff_le (I J : Word (d + 1)) : stratItoCoeff I J ≤ 2 ^ I.length := by
  unfold stratItoCoeff
  set L := ((contractions I).tail.filter (fun p => decide (p.2 = J))).map Prod.fst
  have h1 : L.sum ≤ L.length • (1 : ℝ) := by
    refine List.sum_le_length_nsmul L 1 fun x hx => ?_
    obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hx
    exact (mem_contractions (List.mem_of_mem_tail (List.mem_filter.1 hp).1)).2.1
  have h2 : L.length ≤ 2 ^ I.length := by
    simp only [L, List.length_map]
    calc _ ≤ (contractions I).tail.length := List.length_filter_le _ _
      _ ≤ (contractions I).length := by simp
      _ ≤ _ := length_contractions_le I
  calc L.sum ≤ L.length • (1 : ℝ) := h1
    _ = (L.length : ℝ) := by simp
    _ ≤ 2 ^ I.length := by exact_mod_cast h2

lemma exists_of_stratItoCoeff_ne_zero {I J : Word (d + 1)} (h : stratItoCoeff I J ≠ 0) :
    ∃ p ∈ (contractions I).tail, p.2 = J := by
  by_contra hne
  push Not at hne
  apply h
  unfold stratItoCoeff
  rw [List.filter_eq_nil_iff.2 (fun p hp => by simpa using hne p hp)]
  rfl

lemma length_le_two_mul_of_stratItoCoeff_ne_zero {I J : Word (d + 1)}
    (h : stratItoCoeff I J ≠ 0) : I.length ≤ 2 * J.length := by
  obtain ⟨p, hp, rfl⟩ := exists_of_stratItoCoeff_ne_zero h
  exact (mem_contractions (List.mem_of_mem_tail hp)).2.2.2

/-- Regroup a weighted word list by words. -/
lemma sum_range_sum_wordsOfLength_coeff (L : List (ℝ × Word (d + 1))) (n : ℕ)
    (hL : ∀ p ∈ L, p.2.length < n) (f : Word (d + 1) → ℝ) :
    ∑ m ∈ Finset.range n, ∑ J ∈ wordsOfLength (d + 1) m,
        ((L.filter (fun p => decide (p.2 = J))).map Prod.fst).sum * f J =
      (L.map (fun p => p.1 * f p.2)).sum := by
  classical
  induction L with
  | nil => simp
  | cons p L ih =>
    have ih' := ih fun q hq => hL q (List.mem_cons_of_mem _ hq)
    have hp := hL p List.mem_cons_self
    have e : ∀ J : Word (d + 1),
        (((p :: L).filter (fun p => decide (p.2 = J))).map Prod.fst).sum * f J =
          (if p.2 = J then p.1 * f p.2 else 0) +
            ((L.filter (fun p => decide (p.2 = J))).map Prod.fst).sum * f J := by
      intro J
      by_cases h : p.2 = J
      · subst h; simp [add_mul]
      · simp [h]
    simp only [e, Finset.sum_add_distrib, ih', List.map_cons, List.sum_cons]
    congr 1
    simp only [Finset.sum_ite_eq, wordsOfLength.mem]
    simp [hp]

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

/-- List form of the conversion correction. -/
lemma stratItoCorrection_eq_list (B : MultiBrownian Ω P d) (s t : ℝ) (ω : Ω)
    (K : Word (d + 1)) :
    stratItoCorrection B s t ω K =
      ((contractions K).tail.map (fun p => p.1 * itoWordIntegral B s t ω p.2)).sum := by
  match K with
  | [] => simp [stratItoCorrection, contractions]
  | [_] => simp [stratItoCorrection, contractions]
  | j :: j' :: K =>
    simp only [stratItoCorrection, stratItoCoeff]
    exact sum_range_sum_wordsOfLength_coeff _ _
      (fun p hp => length_lt_of_mem_tail_contractions hp) _

/-- List form of the Stratonovich coordinate: `S^K = Σ_{(c,J) ∈ contractions K} c · I^J`. -/
lemma stratWordIntegral_eq_list (B : MultiBrownian Ω P d) (s t : ℝ) (ω : Ω)
    (K : Word (d + 1)) :
    stratWordIntegral B s t ω K =
      ((contractions K).map (fun p => p.1 * itoWordIntegral B s t ω p.2)).sum := by
  rw [stratWordIntegral, stratItoCorrection_eq_list]
  conv_rhs => rw [contractions_eq_cons K]
  simp

end SignatureVolatility
