module

public import SignatureVolatility.ProlongedBrownianSetup.ItoWordIntegral
public import SignatureVolatility.WordsOfLength


@[expose] public section

open MeasureTheory

noncomputable section

namespace SignatureVolatility

/-!
# Triangular Stratonovich ↔ Itô conversion for prolonged signature coordinates

Paper Appendix (“Detailed Stratonovich–Itô conversion”): for each word `I`,

\[
S^I_t = I^I_t + \sum_{J:|J|<|I|} a_{I,J}\, I^J_t,
\]

with combinatorial coefficients `a_{I,J}` from non-overlapping adjacent equal space-letter
bracket contractions (each replaced by a time letter `0`, weight `(1/2)^|Γ|`).
Level `≤ 1` has no correction (Stratonovich = Itô). The dual/generator shadow of the
leading double-space contraction is `stratonovichHalfLaplacian` (used in Riccati).
-/

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {d : ℕ}

/-- True when `k` starts an adjacent equal space-letter pair in `I`. -/
def canContractAt (I : Word (d + 1)) (k : ℕ) : Bool :=
  if h : k + 1 < I.length then
    decide (I[k]'(Nat.lt_of_succ_lt h) = I[k + 1]'h) &&
      decide ((I[k]'(Nat.lt_of_succ_lt h) : ℕ) ≠ 0)
  else
    false

/-- `ks` indexes non-overlapping adjacent equal space letters in `I`. -/
def isValidContractionSet (I : Word (d + 1)) (ks : Finset ℕ) : Bool :=
  decide
    ((∀ k ∈ ks, canContractAt I k = true) ∧
      (∀ k₁ ∈ ks, ∀ k₂ ∈ ks, k₁ < k₂ → k₁ + 1 < k₂))

/-- All valid contraction index sets for `I` (subsets of `range I.length`). -/
def validContractionFinset (I : Word (d + 1)) : Finset (Finset ℕ) :=
  (Finset.range I.length).powerset.filter fun ks => isValidContractionSet I ks

/-- Replace the pair at start index `k` by the time letter `0`. -/
def contractAt (w : Word (d + 1)) (k : ℕ) : Word (d + 1) :=
  w.take k ++ [(0 : Fin (d + 1))] ++ w.drop (k + 2)

/-- Apply contractions right-to-left so earlier indices stay valid. -/
def applyContractions (I : Word (d + 1)) (ks : Finset ℕ) : Word (d + 1) :=
  (ks.sort (· ≤ ·)).reverse.foldl contractAt I

/-- Combinatorial conversion coefficient `a_{I,J}` (Appendix); empty `Γ` excluded. -/
def stratItoCoeff (I J : Word (d + 1)) : ℝ :=
  ∑ ks ∈ validContractionFinset I,
    if ks.Nonempty ∧ applyContractions I ks = J then (1 / 2 : ℝ) ^ ks.card else 0

/-- Correction polynomial. Vanishes for `|I| ≤ 1`; for longer words, finite sum of
`stratItoCoeff I J * itoWordIntegral … J` over `|J| < |I|`. -/
def stratItoCorrection (B : MultiBrownian Ω P d) (s t : ℝ) (ω : Ω) :
    Word (d + 1) → ℝ
  | [] => 0
  | [_] => 0
  | I@(_ :: _ :: _) =>
      ∑ n ∈ Finset.range I.length,
        ∑ J ∈ wordsOfLength (d + 1) n,
          stratItoCoeff I J * itoWordIntegral B s t ω J

lemma stratItoCorrection_of_length_le_one (B : MultiBrownian Ω P d) (s t : ℝ) (ω : Ω)
    (I : Word (d + 1)) (hI : I.length ≤ 1) :
    stratItoCorrection B s t ω I = 0 := by
  match I with
  | [] => rfl
  | [_] => rfl
  | _ :: _ :: _ =>
    simp at hI

/-- Stratonovich word coordinate via triangular conversion from Itô. -/
def stratWordIntegral (B : MultiBrownian Ω P d) (s t : ℝ) (ω : Ω) (I : Word (d + 1)) : ℝ :=
  itoWordIntegral B s t ω I + stratItoCorrection B s t ω I

lemma stratWordIntegral_empty (B : MultiBrownian Ω P d) (s t : ℝ) (ω : Ω) :
    stratWordIntegral B s t ω [] = 1 := by
  simp [stratWordIntegral, itoWordIntegral_empty, stratItoCorrection]

lemma stratWordIntegral_time (B : MultiBrownian Ω P d) (s t : ℝ) (ω : Ω) :
    stratWordIntegral B s t ω [0] = t - s := by
  simp [stratWordIntegral, itoWordIntegral_time, stratItoCorrection]

lemma stratWordIntegral_space (B : MultiBrownian Ω P d) (s t : ℝ) (ω : Ω) (i : Fin d) :
    stratWordIntegral B s t ω [i.succ] =
      MultiBrownian.W B t ω i - MultiBrownian.W B s ω i := by
  simp [stratWordIntegral, itoWordIntegral_space, stratItoCorrection]

lemma measurable_stratItoCorrection (B : MultiBrownian Ω P d) (s t : ℝ)
    (I : Word (d + 1)) :
    Measurable (fun ω => stratItoCorrection B s t ω I) := by
  match I with
  | [] =>
    change Measurable (fun _ => (0 : ℝ))
    exact measurable_const
  | [_] =>
    change Measurable (fun _ => (0 : ℝ))
    exact measurable_const
  | _ :: _ :: _ =>
    simp only [stratItoCorrection]
    exact Finset.measurable_sum _ fun _ _ =>
      Finset.measurable_sum _ fun J _ =>
        (measurable_itoWordIntegral B s t J).const_mul _

lemma measurable_stratWordIntegral (B : MultiBrownian Ω P d) (s t : ℝ) (I : Word (d + 1)) :
    Measurable (fun ω => stratWordIntegral B s t ω I) :=
  (measurable_itoWordIntegral B s t I).add (measurable_stratItoCorrection B s t I)

private lemma applyContractions_singleton_zero (w : Word (d + 1)) :
    applyContractions w {0} = contractAt w 0 := by
  simp only [applyContractions]
  rw [Finset.sort_singleton]
  rfl

private lemma contractAt_diag (i : Fin d) :
    contractAt ([i.succ, i.succ] : Word (d + 1)) 0 = ([0] : Word (d + 1)) :=
  rfl

private lemma canContractAt_diag_zero (i : Fin d) :
    canContractAt ([i.succ, i.succ] : Word (d + 1)) 0 = true := by
  simp [canContractAt]

private lemma canContractAt_diag_one (i : Fin d) :
    canContractAt ([i.succ, i.succ] : Word (d + 1)) 1 = false := by
  simp [canContractAt]

private lemma validContractionFinset_diag_space (i : Fin d) :
    validContractionFinset ([i.succ, i.succ] : Word (d + 1)) = {∅, {0}} := by
  classical
  ext ks
  simp only [validContractionFinset, Finset.mem_filter, Finset.mem_powerset, Finset.mem_insert,
    Finset.mem_singleton]
  constructor
  · rintro ⟨hsub, hval⟩
    have hlen : ([i.succ, i.succ] : Word (d + 1)).length = 2 := rfl
    rw [hlen] at hsub
    have hks : ks ⊆ ({0, 1} : Finset ℕ) := by
      intro x hx
      have : x ∈ Finset.range 2 := hsub hx
      have hxlt : x < 2 := Finset.mem_range.mp this
      interval_cases x <;> simp
    simp only [isValidContractionSet, decide_eq_true_eq] at hval
    obtain ⟨hcan, hnon⟩ := hval
    by_cases h0 : 0 ∈ ks
    · by_cases h1 : 1 ∈ ks
      · -- {0,1}: overlapping fails non-overlap
        have := hnon 0 h0 1 h1 (by decide : (0 : ℕ) < 1)
        simp at this
      · right
        ext x
        constructor
        · intro hx
          have hx' := hks hx
          simp only [Finset.mem_insert, Finset.mem_singleton] at hx' ⊢
          rcases hx' with rfl | rfl
          · simp
          · exact (h1 hx).elim
        · intro hx
          simp only [Finset.mem_singleton] at hx
          simpa [hx] using h0
    · by_cases h1 : 1 ∈ ks
      · -- {1} fails canContractAt
        have := hcan 1 h1
        rw [canContractAt_diag_one i] at this
        cases this
      · left
        ext x
        constructor
        · intro hx
          have hx' := hks hx
          simp only [Finset.mem_insert, Finset.mem_singleton] at hx'
          rcases hx' with rfl | rfl
          · exact (h0 hx).elim
          · exact (h1 hx).elim
        · intro hx
          simp at hx
  · rintro (rfl | rfl)
    · simp [isValidContractionSet]
    · simp [isValidContractionSet, canContractAt_diag_zero i]

/-- Length-2 diagonal: the only nonempty contraction is `{0} ↦ [0]`, weight `1/2`. -/
lemma stratItoCoeff_diag_space (i : Fin d) :
    stratItoCoeff (d := d) ([i.succ, i.succ] : Word (d + 1)) [0] = (1 / 2 : ℝ) := by
  classical
  simp only [stratItoCoeff, validContractionFinset_diag_space i]
  have happ : applyContractions ([i.succ, i.succ] : Word (d + 1)) {0} = [0] := by
    rw [applyContractions_singleton_zero, contractAt_diag]
  simp [happ, Finset.card_singleton]

lemma stratWordIntegral_diag_space (B : MultiBrownian Ω P d) (s t : ℝ) (ω : Ω) (i : Fin d) :
    stratWordIntegral B s t ω [i.succ, i.succ] =
      itoWordIntegral B s t ω [i.succ, i.succ] + (1 / 2 : ℝ) * (t - s) := by
  classical
  simp only [stratWordIntegral, stratItoCorrection]
  change itoWordIntegral B s t ω [i.succ, i.succ] +
      (∑ n ∈ Finset.range 2,
        ∑ J ∈ wordsOfLength (d + 1) n,
          stratItoCoeff ([i.succ, i.succ] : Word (d + 1)) J *
            itoWordIntegral B s t ω J) =
      itoWordIntegral B s t ω [i.succ, i.succ] + (1 / 2 : ℝ) * (t - s)
  congr 1
  rw [Finset.sum_range_succ, Finset.sum_range_one]
  have happ : applyContractions ([i.succ, i.succ] : Word (d + 1)) {0} = [0] := by
    rw [applyContractions_singleton_zero, contractAt_diag]
  have h0 :
      (∑ J ∈ wordsOfLength (d + 1) 0,
          stratItoCoeff ([i.succ, i.succ] : Word (d + 1)) J *
            itoWordIntegral B s t ω J) = 0 := by
    simp only [wordsOfLength, Finset.sum_singleton, stratItoCoeff,
      validContractionFinset_diag_space i]
    simp [happ]
  have h1 :
      (∑ J ∈ wordsOfLength (d + 1) 1,
          stratItoCoeff ([i.succ, i.succ] : Word (d + 1)) J *
            itoWordIntegral B s t ω J) =
        (1 / 2 : ℝ) * (t - s) := by
    rw [wordsOfLength.succ]
    simp only [wordsOfLength, Finset.sum_singleton]
    refine (Finset.sum_eq_single (0 : Fin (d + 1)) ?_ ?_).trans ?_
    · intro j _ hj
      have hc : stratItoCoeff ([i.succ, i.succ] : Word (d + 1)) [j] = 0 := by
        simp only [stratItoCoeff, validContractionFinset_diag_space i]
        have hne : ¬(([0] : Word (d + 1)) = [j]) := fun h =>
          hj (List.cons.inj h).1.symm
        simp [happ, hne]
      simp [hc]
    · intro h
      exact (h (Finset.mem_univ _)).elim
    · simp [stratItoCoeff_diag_space i, itoWordIntegral_time]
  simp [h0, h1]

/-- Package Stratonovich word coordinates as an extended tensor series. -/
def stratSig2 (B : MultiBrownian Ω P d) (s t : ℝ) (ω : Ω) : ExtTensorAlgebra (d + 1) :=
  ⟨fun I => stratWordIntegral B s t ω I⟩

lemma stratSig2_empty (B : MultiBrownian Ω P d) (s t : ℝ) (ω : Ω) :
    (stratSig2 B s t ω).coeff [] = 1 :=
  stratWordIntegral_empty B s t ω

lemma stratSig2_time (B : MultiBrownian Ω P d) (s t : ℝ) (ω : Ω) :
    (stratSig2 B s t ω).coeff [0] = t - s :=
  stratWordIntegral_time B s t ω

lemma stratSig2_space (B : MultiBrownian Ω P d) (s t : ℝ) (ω : Ω) (i : Fin d) :
    (stratSig2 B s t ω).coeff [i.succ] =
      MultiBrownian.W B t ω i - MultiBrownian.W B s ω i :=
  stratWordIntegral_space B s t ω i

lemma measurable_stratSig2_coeff (B : MultiBrownian Ω P d) (s t : ℝ) (I : Word (d + 1)) :
    Measurable (fun ω => (stratSig2 B s t ω).coeff I) :=
  measurable_stratWordIntegral B s t I

end SignatureVolatility
