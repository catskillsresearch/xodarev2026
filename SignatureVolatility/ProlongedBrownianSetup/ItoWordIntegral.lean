module

public import SignatureVolatility.ExtTensorAlgebra.ExtTensorAlgebra
public import SignatureVolatility.ProlongedBrownianSetup.OfBrownian
public import SignatureVolatility.Word


@[expose] public section

open MeasureTheory

noncomputable section

namespace SignatureVolatility

/-!
# Word-indexed Itô iterated integrals of the prolonged path `(t, W)`

Recursive Itô signature coordinates of `MultiBrownian.wAug`. Level `≤ 1` is explicit
(Lebesgue time / Brownian increment). Longer words integrate the previous coordinate against
the corresponding letter of `wAug` in the Itô sense (Lebesgue for the time letter; MathFin
Itô against `W^i` for space letters).

**Status.** Empty and length-1 clauses are proved. The recursive Itô step
(`itoWordIntegral_cons`) is the MathFin wiring hole for words of length `≥ 2`.
-/

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {d : ℕ}

/-- Space letter `j : Fin (d+1)` with `j ≠ 0` as a Brownian coordinate index. -/
def spaceLetterIndex (j : Fin (d + 1)) (hj : (j : ℕ) ≠ 0) : Fin d :=
  ⟨j.1 - 1, by
    have : j.1 < d + 1 := j.isLt
    omega⟩

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
  match I with
  | [] => simp [itoWordIntegral_le1]
  | j :: I' =>
    simp only [itoWordIntegral_le1]
    by_cases hI : I' ≠ []
    · simp [hI]
    · simp only [hI, ↓reduceIte]
      by_cases hj : (j : ℕ) = 0
      · simp [hj]
      · simp only [hj, ↓reduceDIte]
        exact (MultiBrownian.W_meas B t (spaceLetterIndex j hj)).sub
          (MultiBrownian.W_meas B s (spaceLetterIndex j hj))

/-- Recursive Itô step: integrate previous word coordinate against letter `j` of `wAug`.

* Time letter (`j = 0`): Lebesgue `∫_s^t` of the previous coordinate.
* Space letter: MathFin Itô integral against `W^i` on `[s,t]`.

MathFin wiring + progressive measurability of the integrand: HOLE. -/
def itoWordIntegral_cons (B : MultiBrownian Ω P d) (j : Fin (d + 1)) (I : Word (d + 1))
    (s t : ℝ) (ω : Ω) : ℝ := by
  sorry

/-- Word-indexed Itô iterated integral of `wAug` over `[s,t]`. -/
def itoWordIntegral (B : MultiBrownian Ω P d) (s t : ℝ) (ω : Ω) : Word (d + 1) → ℝ
  | [] => 1
  | j :: I =>
    if I = [] then itoWordIntegral_le1 B s t ω [j]
    else itoWordIntegral_cons B j I s t ω

lemma itoWordIntegral_empty (B : MultiBrownian Ω P d) (s t : ℝ) (ω : Ω) :
    itoWordIntegral B s t ω [] = 1 := rfl

lemma itoWordIntegral_time (B : MultiBrownian Ω P d) (s t : ℝ) (ω : Ω) :
    itoWordIntegral B s t ω [0] = t - s := by
  simp [itoWordIntegral, itoWordIntegral_le1_time]

lemma itoWordIntegral_space (B : MultiBrownian Ω P d) (s t : ℝ) (ω : Ω) (i : Fin d) :
    itoWordIntegral B s t ω [i.succ] =
      MultiBrownian.W B t ω i - MultiBrownian.W B s ω i := by
  simp [itoWordIntegral, itoWordIntegral_le1_space]

lemma measurable_itoWordIntegral (B : MultiBrownian Ω P d) (s t : ℝ) (I : Word (d + 1)) :
    Measurable (fun ω => itoWordIntegral B s t ω I) := by
  match I with
  | [] => simp [itoWordIntegral]
  | j :: I' =>
    by_cases hI : I' = []
    · subst hI
      simpa [itoWordIntegral] using measurable_itoWordIntegral_le1 B s t [j]
    · simp only [itoWordIntegral, hI, ↓reduceIte]
      -- Needs adaptedness of `itoWordIntegral_cons` once MathFin-wired.
      sorry

/-- Package Itô word coordinates as an element of the extended tensor algebra. -/
def itoSig2 (B : MultiBrownian Ω P d) (s t : ℝ) (ω : Ω) : ExtTensorAlgebra (d + 1) :=
  ⟨fun I => itoWordIntegral B s t ω I⟩

lemma itoSig2_empty (B : MultiBrownian Ω P d) (s t : ℝ) (ω : Ω) :
    (itoSig2 B s t ω).coeff [] = 1 :=
  itoWordIntegral_empty B s t ω

lemma itoSig2_time (B : MultiBrownian Ω P d) (s t : ℝ) (ω : Ω) :
    (itoSig2 B s t ω).coeff [0] = t - s :=
  itoWordIntegral_time B s t ω

lemma itoSig2_space (B : MultiBrownian Ω P d) (s t : ℝ) (ω : Ω) (i : Fin d) :
    (itoSig2 B s t ω).coeff [i.succ] =
      MultiBrownian.W B t ω i - MultiBrownian.W B s ω i :=
  itoWordIntegral_space B s t ω i

lemma measurable_itoSig2_coeff (B : MultiBrownian Ω P d) (s t : ℝ) (I : Word (d + 1)) :
    Measurable (fun ω => (itoSig2 B s t ω).coeff I) :=
  measurable_itoWordIntegral B s t I

end SignatureVolatility
