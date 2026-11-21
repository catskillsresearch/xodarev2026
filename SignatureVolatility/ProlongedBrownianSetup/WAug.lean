import SignatureVolatility.ProlongedBrownianSetup

open MeasureTheory

noncomputable section

namespace SignatureVolatility

namespace ProlongedBrownianSetup

variable {Ω : Type*} [m₀ : MeasurableSpace Ω] {ℙ : Measure Ω} [IsProbabilityMeasure ℙ]
  {d : ℕ} {T : ℝ}

def W_aug (setup : ProlongedBrownianSetup Ω ℙ d T) (t : ℝ) (ω : Ω) : Fin (d + 1) → ℝ :=
  Fin.cases t (fun i => setup.W t ω i)

end ProlongedBrownianSetup

end SignatureVolatility
