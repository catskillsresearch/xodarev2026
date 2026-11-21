module

public import SignatureVolatility.ProlongedBrownianSetup.ItoIntegralAgainstBM
public import SignatureVolatility.ProlongedBrownianSetup.ItoWordIntegralLe1


@[expose] public section

open MeasureTheory

noncomputable section

namespace SignatureVolatility

/-!
# Longer-word Itô recursion (`|I| ≥ 2`)

**Status: HOLE.** Needs inductive predictability of previous-word coordinates as MathFin
integrands (time letter via Lebesgue; space letter via `localItoIntegral` / dyadic Itô limits).
-/

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {d : ℕ}

/-- Recursive Itô step for previous words of length `≥ 2`. -/
def itoWordIntegral_cons_long (B : MultiBrownian Ω P d) (j : Fin (d + 1)) (I : Word (d + 1))
    (s t : ℝ) (ω : Ω) : ℝ := by
  -- Time: `∫_s^t itoWordIntegral B s u ω I du`
  -- Space: MathFin Ito of that process against `Wnn (spaceLetterIndex j _)`
  sorry

lemma measurable_itoWordIntegral_cons_long (B : MultiBrownian Ω P d) (j : Fin (d + 1))
    (I : Word (d + 1)) (s t : ℝ) :
    Measurable (fun ω => itoWordIntegral_cons_long B j I s t ω) := by
  sorry

end SignatureVolatility
