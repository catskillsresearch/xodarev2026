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

/-- Weighted contraction list of `I` (paper Appendix): every choice `Γ` of non-overlapping
adjacent equal space-letter pairs, each pair replaced by the time letter `0`, paired with its
weight `(1/2)^|Γ|`. Built by recursion on the first letter: either it is left alone, or (when
it is a space letter equal to the next one) the first pair is contracted. The head entry is the
empty contraction `(1, I)`. -/
def contractions : Word (d + 1) → List (ℝ × Word (d + 1))
  | [] => [(1, [])]
  | [j] => [(1, [j])]
  | j :: j' :: K =>
      (contractions (j' :: K)).map (fun p => (p.1, j :: p.2)) ++
        (if j = j' ∧ (j : ℕ) ≠ 0 then
          (contractions K).map (fun p => (p.1 / 2, (0 : Fin (d + 1)) :: p.2)) else [])

/-- Combinatorial conversion coefficient `a_{I,J}` (Appendix); empty `Γ` excluded. -/
def stratItoCoeff (I J : Word (d + 1)) : ℝ :=
  (((contractions I).tail.filter (fun p => decide (p.2 = J))).map Prod.fst).sum

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
  cases I with
  | nil =>
    change Measurable (fun _ => (0 : ℝ))
    exact measurable_const
  | cons _ I' =>
    cases I' with
    | nil =>
      change Measurable (fun _ => (0 : ℝ))
      exact measurable_const
    | cons _ _ =>
      simp only [stratItoCorrection]
      exact Finset.measurable_sum _ fun _ _ =>
        Finset.measurable_sum _ fun J _ =>
          (measurable_itoWordIntegral B s t J).const_mul _

lemma measurable_stratWordIntegral (B : MultiBrownian Ω P d) (s t : ℝ) (I : Word (d + 1)) :
    Measurable (fun ω => stratWordIntegral B s t ω I) :=
  (measurable_itoWordIntegral B s t I).add (measurable_stratItoCorrection B s t I)

lemma stratWordIntegral_diag_space (B : MultiBrownian Ω P d) (s t : ℝ) (ω : Ω) (i : Fin d) :
    stratWordIntegral B s t ω [i.succ, i.succ] =
      itoWordIntegral B s t ω [i.succ, i.succ] + (1 / 2 : ℝ) * (t - s) := by
  classical
  have hc : ∀ J : Word (d + 1), stratItoCoeff ([i.succ, i.succ] : Word (d + 1)) J =
      if ([0] : Word (d + 1)) = J then 1 / 2 else 0 := by
    intro J
    have hne : ((i.succ : Fin (d + 1)) : ℕ) ≠ 0 := by simp
    simp only [stratItoCoeff, contractions, hne, and_self, ite_true, ne_eq, not_false_eq_true]
    by_cases h : ([0] : Word (d + 1)) = J <;> simp [h]
  simp only [stratWordIntegral, stratItoCorrection]
  change itoWordIntegral B s t ω [i.succ, i.succ] +
      (∑ n ∈ Finset.range 2,
        ∑ J ∈ wordsOfLength (d + 1) n,
          stratItoCoeff ([i.succ, i.succ] : Word (d + 1)) J *
            itoWordIntegral B s t ω J) =
      itoWordIntegral B s t ω [i.succ, i.succ] + (1 / 2 : ℝ) * (t - s)
  congr 1
  simp only [hc, ite_mul, zero_mul]
  rw [Finset.sum_range_succ, Finset.sum_range_one]
  simp only [Finset.sum_ite_eq, wordsOfLength.mem, List.length_singleton]
  simp [itoWordIntegral_time]

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
