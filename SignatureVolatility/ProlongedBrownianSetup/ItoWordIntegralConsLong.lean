module

public import SignatureVolatility.ProlongedBrownianSetup.ItoIntegralProcess
public import SignatureVolatility.ProlongedBrownianSetup.ItoWordIntegralLe1


@[expose] public section

open MeasureTheory

noncomputable section

namespace SignatureVolatility

/-!
# Longer-word Itô recursion (`|I| ≥ 2`)

One-step integrator: previous word coordinate arrives as a process `H`, integrated against
time (Lebesgue) or a Brownian letter (dyadic Itô) via `ItoIntegralProcess`.
-/

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {d : ℕ}

/-- Recursive Itô step for previous words of length `≥ 2`, given as process `H`. -/
def itoWordIntegral_cons_long (B : MultiBrownian Ω P d) (j : Fin (d + 1))
    (H : ℝ → Ω → ℝ) (s t : ℝ) (ω : Ω) : ℝ :=
  if hj : (j : ℕ) = 0 then lebIntegral_process H s t ω
  else itoIntegral_process B (spaceLetterIndex j hj) H s t ω

lemma measurable_itoWordIntegral_cons_long (B : MultiBrownian Ω P d) (j : Fin (d + 1))
    (H : ℝ → Ω → ℝ) (hH : ∀ u, Measurable (H u)) (s t : ℝ) :
    Measurable (fun ω => itoWordIntegral_cons_long B j H s t ω) := by
  simp only [itoWordIntegral_cons_long]
  by_cases hj : (j : ℕ) = 0
  · simpa [hj] using measurable_lebIntegral_process H hH s t
  · simpa [hj] using measurable_itoIntegral_process B (spaceLetterIndex j hj) H hH s t

end SignatureVolatility
