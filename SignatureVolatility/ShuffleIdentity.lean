module

public import SignatureVolatility.ExtTensorAlgebra.EvalShuffleBasis
public import SignatureVolatility.Letter
public import SignatureVolatility.ProlongedBrownianSetup
public import SignatureVolatility.ProlongedBrownianSetup.WHat
public import SignatureVolatility.Word


@[expose] public section

noncomputable section

open MeasureTheory

namespace SignatureVolatility

namespace ProlongedBrownianSetup

variable {Ω : Type*} [m₀ : MeasurableSpace Ω] {ℙ : Measure Ω} [IsProbabilityMeasure ℙ]
  {d : ℕ} {T : ℝ}

theorem shuffle_identity (setup : ProlongedBrownianSetup Ω ℙ d T)
    {t : ℝ} (ht0 : 0 ≤ t) (htT : t ≤ T) (I J : Word (d + 1)) (ω : Ω) :
    (setup.W_hat t ω).coeff I * (setup.W_hat t ω).coeff J =
      ExtTensorAlgebra.evalShuffleBasis I J (setup.W_hat t ω) :=
  setup.stratonovich_shuffle ht0 htT I J ω

end ProlongedBrownianSetup

end SignatureVolatility
