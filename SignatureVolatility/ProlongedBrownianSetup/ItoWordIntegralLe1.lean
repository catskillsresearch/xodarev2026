module

public import SignatureVolatility.ExtTensorAlgebra.ExtTensorAlgebra
public import SignatureVolatility.ProlongedBrownianSetup.OfBrownian
public import SignatureVolatility.Word


@[expose] public section

open MeasureTheory

noncomputable section

namespace SignatureVolatility

/-!
# Level-≤1 Itô word coordinates of `wAug`
-/

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {d : ℕ}

/-- Space letter `j : Fin (d+1)` with `j ≠ 0` as a Brownian coordinate index. -/
def spaceLetterIndex (j : Fin (d + 1)) (hj : (j : ℕ) ≠ 0) : Fin d :=
  ⟨j.1 - 1, (Nat.sub_lt_iff_lt_add (Nat.one_le_iff_ne_zero.mpr hj)).mpr
    j.isLt⟩

/-- Level-1 (and empty) Itô coordinates of `wAug`, fully explicit. -/
def itoWordIntegral_le1 (B : MultiBrownian Ω P d) (s t : ℝ) (ω : Ω) :
    Word (d + 1) → ℝ
  | [] => 1
  | j :: I =>
    if I ≠ [] then 0
    else if h : (j : ℕ) = 0 then t - s
    else
      MultiBrownian.W B t ω (spaceLetterIndex j h) -
        MultiBrownian.W B s ω (spaceLetterIndex j h)

lemma itoWordIntegral_le1_empty (B : MultiBrownian Ω P d) (s t : ℝ) (ω : Ω) :
    itoWordIntegral_le1 B s t ω [] = 1 := rfl

lemma itoWordIntegral_le1_time (B : MultiBrownian Ω P d) (s t : ℝ) (ω : Ω) :
    itoWordIntegral_le1 B s t ω [0] = t - s := by
  simp [itoWordIntegral_le1]

lemma itoWordIntegral_le1_space (B : MultiBrownian Ω P d) (s t : ℝ) (ω : Ω) (i : Fin d) :
    itoWordIntegral_le1 B s t ω [i.succ] = MultiBrownian.W B t ω i - MultiBrownian.W B s ω i := by
  simp [itoWordIntegral_le1, spaceLetterIndex, Fin.val_succ]

lemma measurable_itoWordIntegral_le1 (B : MultiBrownian Ω P d) (s t : ℝ) (I : Word (d + 1)) :
    Measurable (fun ω => itoWordIntegral_le1 B s t ω I) := by
  cases I with
  | nil => simp [itoWordIntegral_le1]
  | cons j I' =>
    simp only [itoWordIntegral_le1]
    by_cases hI : I' ≠ []
    · simp [hI]
    · simp only [hI, ↓reduceIte]
      by_cases hj : (j : ℕ) = 0
      · simp [hj]
      · simp only [hj, ↓reduceDIte]
        exact (MultiBrownian.W_meas B t (spaceLetterIndex j hj)).sub
          (MultiBrownian.W_meas B s (spaceLetterIndex j hj))

end SignatureVolatility
