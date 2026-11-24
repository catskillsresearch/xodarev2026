module

public import SignatureVolatility.ProlongedBrownianSetup.StratonovichItoConversion

@[expose] public section


namespace SignatureVolatility

/-!
# Size bounds for the Stratonovich–Itô conversion coefficients

`0 ≤ a_{K,J} ≤ 2^{|K|}` and `a_{K,J} ≠ 0 → |K| ≤ 2 |J|`: each contraction removes one letter and
the contracted pairs are disjoint.
-/

variable {d : ℕ}

lemma length_contractAt_add_one (w : Word (d + 1)) (k : ℕ) :
    w.length ≤ (contractAt w k).length + 1 := by
  simp only [contractAt, List.length_append, List.length_take, List.length_cons,
    List.length_nil, List.length_drop]
  omega

lemma length_foldl_contractAt (L : List ℕ) :
    ∀ w : Word (d + 1), w.length ≤ (L.foldl contractAt w).length + L.length := by
  induction L with
  | nil => intro w; simp
  | cons k L ih =>
    intro w
    have h1 := length_contractAt_add_one w k
    have h2 := ih (contractAt w k)
    simp only [List.foldl_cons, List.length_cons]
    omega

lemma length_applyContractions (I : Word (d + 1)) (ks : Finset ℕ) :
    I.length ≤ (applyContractions I ks).length + ks.card := by
  have := length_foldl_contractAt ((ks.sort (· ≤ ·)).reverse) I
  simpa [applyContractions, List.length_reverse, Finset.length_sort] using this

lemma lt_length_of_canContractAt {I : Word (d + 1)} {k : ℕ} (h : canContractAt I k = true) :
    k + 1 < I.length := by
  unfold canContractAt at h
  split_ifs at h with hk
  exact hk

lemma two_mul_card_le_of_valid {I : Word (d + 1)} {ks : Finset ℕ}
    (h : isValidContractionSet I ks = true) : 2 * ks.card ≤ I.length := by
  unfold isValidContractionSet at h
  rw [decide_eq_true_iff] at h
  obtain ⟨hc, hgap⟩ := h
  have hdisj : Disjoint ks (ks.image (· + 1)) := by
    rw [Finset.disjoint_left]
    intro a ha hb
    obtain ⟨b, hb', rfl⟩ := Finset.mem_image.1 hb
    have := hgap b hb' (b + 1) ha (by omega)
    omega
  have hcard : (ks ∪ ks.image (· + 1)).card = 2 * ks.card := by
    rw [Finset.card_union_of_disjoint hdisj,
      Finset.card_image_of_injective _ (add_left_injective 1)]
    ring
  have hsub : ks ∪ ks.image (· + 1) ⊆ Finset.range I.length := by
    intro a ha
    rw [Finset.mem_union] at ha
    rw [Finset.mem_range]
    rcases ha with ha | ha
    · have := lt_length_of_canContractAt (hc a ha); omega
    · obtain ⟨b, hb, rfl⟩ := Finset.mem_image.1 ha
      exact lt_length_of_canContractAt (hc b hb)
  rw [← hcard]
  simpa using Finset.card_le_card hsub

lemma stratItoCoeff_nonneg (I J : Word (d + 1)) : 0 ≤ stratItoCoeff I J :=
  Finset.sum_nonneg fun ks _ => by split_ifs <;> positivity

lemma stratItoCoeff_le (I J : Word (d + 1)) : stratItoCoeff I J ≤ 2 ^ I.length := by
  calc stratItoCoeff I J ≤ ∑ _ks ∈ validContractionFinset I, (1 : ℝ) := by
        apply Finset.sum_le_sum
        intro ks _
        split_ifs
        · exact pow_le_one₀ (by norm_num) (by norm_num)
        · exact zero_le_one
    _ = (validContractionFinset I).card := by simp
    _ ≤ ((Finset.range I.length).powerset).card := by
        exact_mod_cast Finset.card_le_card (Finset.filter_subset _ _)
    _ = 2 ^ I.length := by simp

lemma length_le_two_mul_of_stratItoCoeff_ne_zero {I J : Word (d + 1)}
    (h : stratItoCoeff I J ≠ 0) : I.length ≤ 2 * J.length := by
  obtain ⟨ks, hks, hne⟩ := Finset.exists_ne_zero_of_sum_ne_zero h
  have hv : isValidContractionSet I ks = true := (Finset.mem_filter.1 hks).2
  split_ifs at hne with hc
  · have h1 := length_applyContractions I ks
    rw [hc.2] at h1
    have h2 := two_mul_card_le_of_valid hv
    omega
  · exact absurd rfl hne

end SignatureVolatility
