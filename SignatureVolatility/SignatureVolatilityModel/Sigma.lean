import SignatureVolatility.SignatureVolatilityModel
import SignatureVolatility.ProlongedBrownianSetup
import SignatureVolatility.ProlongedBrownianSetup.WHat
import SignatureVolatility.DualPairing
import SignatureVolatility.ExtTensorAlgebra.LevelInner


open scoped BigOperators Classical ENNReal NNReal RealInnerProductSpace
open MeasureTheory Filter Topology Set

noncomputable section

namespace SignatureVolatility

namespace SignatureVolatilityModel

def sigma {Ω : Type*} [MeasurableSpace Ω] {ℙ : Measure Ω} [IsProbabilityMeasure ℙ]
    (M : SignatureVolatilityModel) (setup : ProlongedBrownianSetup Ω ℙ M.d M.T)
    (t : ℝ) (ω : Ω) : ℝ :=
  dualPairing M.ℓ (setup.W_hat t ω)

end SignatureVolatilityModel

end SignatureVolatility
