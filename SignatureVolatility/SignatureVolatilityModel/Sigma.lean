module

public import SignatureVolatility.DualPairing
public import SignatureVolatility.ExtTensorAlgebra.LevelInner
public import SignatureVolatility.ProlongedBrownianSetup
public import SignatureVolatility.ProlongedBrownianSetup.WHat
public import SignatureVolatility.SignatureVolatilityModel


@[expose] public section

noncomputable section

open MeasureTheory

namespace SignatureVolatility

namespace SignatureVolatilityModel

def sigma {Ω : Type*} [MeasurableSpace Ω] {ℙ : Measure Ω} [IsProbabilityMeasure ℙ]
    (M : SignatureVolatilityModel) (setup : ProlongedBrownianSetup Ω ℙ M.d M.T)
    (t : ℝ) (ω : Ω) : ℝ :=
  dualPairing M.ℓ (setup.W_hat t ω)

end SignatureVolatilityModel

end SignatureVolatility
