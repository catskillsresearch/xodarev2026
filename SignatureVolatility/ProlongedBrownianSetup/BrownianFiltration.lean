module

public import SignatureVolatility.ProlongedBrownianSetup
public import SignatureVolatility.GeneratedFiltration
public import SignatureVolatility.IndexedFiltration


@[expose] public section

open scoped BigOperators Classical ENNReal NNReal RealInnerProductSpace
open MeasureTheory Filter Topology Set

noncomputable section

namespace SignatureVolatility

namespace ProlongedBrownianSetup

variable {Ω : Type*} [m₀ : MeasurableSpace Ω] {ℙ : Measure Ω} [IsProbabilityMeasure ℙ]
  {d : ℕ} {T : ℝ}

def brownianFiltration (setup : ProlongedBrownianSetup Ω ℙ d T) : IndexedFiltration Ω :=
  generatedFiltration (fun u i ω => setup.W u ω i) setup.W_meas

end ProlongedBrownianSetup

end SignatureVolatility
