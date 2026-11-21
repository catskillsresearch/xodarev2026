import SignatureVolatility.ProlongedBrownianSetup
import SignatureVolatility.ExtTensorAlgebra.Concat

open MeasureTheory

noncomputable section

namespace SignatureVolatility

namespace ProlongedBrownianSetup

variable {Ω : Type*} [m₀ : MeasurableSpace Ω] {ℙ : Measure Ω} [IsProbabilityMeasure ℙ]
  {d : ℕ} {T : ℝ}

theorem chen_identity (setup : ProlongedBrownianSetup Ω ℙ d T)
    {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) (ht : t ≤ T) (ω : Ω) :
    setup.sig2 0 t ω = setup.sig2 0 s ω ⊗ₜ setup.sig2 s t ω :=
  setup.stratonovich_chen hs hst ht ω

end ProlongedBrownianSetup

end SignatureVolatility
