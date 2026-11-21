module

public import Mathlib

@[expose] public section

open MeasureTheory

noncomputable section

namespace SignatureVolatility

def AdmissibleGainsUnderP {Ω : Type*} [MeasurableSpace Ω] (ℙ : Measure Ω) : Set (Ω → ℝ) :=
  {G | Integrable G ℙ ∧ ∫ ω, G ω ∂ℙ ≤ 0}

end SignatureVolatility
