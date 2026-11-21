import SignatureVolatility.ProlongedBrownianSetup


open scoped BigOperators Classical ENNReal NNReal RealInnerProductSpace
open MeasureTheory Filter Topology Set

noncomputable section

namespace SignatureVolatility

namespace ProlongedBrownianSetup

variable {Ω : Type*} [m₀ : MeasurableSpace Ω] {ℙ : Measure Ω} [IsProbabilityMeasure ℙ]
  {d : ℕ} {T : ℝ}

def W_hat (setup : ProlongedBrownianSetup Ω ℙ d T) (t : ℝ) (ω : Ω) :
    ExtTensorAlgebra (d + 1) :=
  setup.sig2 0 t ω

end ProlongedBrownianSetup

end SignatureVolatility
