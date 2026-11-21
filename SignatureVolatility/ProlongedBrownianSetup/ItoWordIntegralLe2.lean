module

public import SignatureVolatility.ProlongedBrownianSetup.ItoIntegralAgainstBM
public import SignatureVolatility.ProlongedBrownianSetup.ItoWordIntegralLe1


@[expose] public section

open MeasureTheory

noncomputable section

namespace SignatureVolatility

/-!
# Length-2 Itô word step

`itoWordIntegral_le2` evaluates the Itô step when the previous word has length 1.
-/

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {d : ℕ}

/-- Previous letter of a length-1 word. -/
def lengthOneLetter (I : Word (d + 1)) (hI : I.length = 1) : Fin (d + 1) :=
  I[0]'(by omega)

/-- Length-2 Itô step: previous word `I` has length 1. -/
def itoWordIntegral_le2 (B : MultiBrownian Ω P d) (j : Fin (d + 1)) (I : Word (d + 1))
    (hI : I.length = 1) (s t : ℝ) (ω : Ω) : ℝ :=
  let j' := lengthOneLetter I hI
  if hj : (j : ℕ) = 0 then
    if hj' : (j' : ℕ) = 0 then lebIntegral_timeIntegrand s t
    else lebIntegral_wnnIncrement B (spaceLetterIndex j' hj') s t ω
  else if hj' : (j' : ℕ) = 0 then
    itoIntegral_timeIntegrand B (spaceLetterIndex j hj) s t ω
  else
    itoIntegral_wnnIncrement B (spaceLetterIndex j' hj') (spaceLetterIndex j hj) s t ω

lemma measurable_itoWordIntegral_le2 (B : MultiBrownian Ω P d) (j : Fin (d + 1))
    (I : Word (d + 1)) (hI : I.length = 1) (s t : ℝ) :
    Measurable (fun ω => itoWordIntegral_le2 B j I hI s t ω) := by
  simp only [itoWordIntegral_le2]
  by_cases hj : (j : ℕ) = 0
  · simp only [hj, ↓reduceDIte]
    by_cases hj' : ((lengthOneLetter I hI) : ℕ) = 0
    · simp [hj']
    · simpa [hj'] using
        measurable_lebIntegral_wnnIncrement B (spaceLetterIndex (lengthOneLetter I hI) hj') s t
  · simp only [hj, ↓reduceDIte]
    by_cases hj' : ((lengthOneLetter I hI) : ℕ) = 0
    · simpa [hj'] using measurable_itoIntegral_timeIntegrand B (spaceLetterIndex j hj) s t
    · simpa [hj'] using measurable_itoIntegral_wnnIncrement B
        (spaceLetterIndex (lengthOneLetter I hI) hj') (spaceLetterIndex j hj) s t

end SignatureVolatility
