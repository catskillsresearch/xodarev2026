module

public import SignatureVolatility.GKWDecompositionSetup
public import SignatureVolatility.PriceFiltrationSignatureSpace.OfMarket
public import SignatureVolatility.Weight


@[expose] public section

open MeasureTheory Set

namespace SignatureVolatility

/-!
# Paper-strength `GKWDecompositionSetup` (Phase 4 / Theorem D)

**Status: HOLE.** Kit inhabitant only. Paper Theorem D lives in `TheoremD`.
-/

/-- **Paper goal.** GKW package over a market-built PFS. -/
noncomputable def gkwDecompositionSetup_of_pfs
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    (mkt : MarketData Ω P) (w : Weight) :
    GKWDecompositionSetup ℝ mkt.M.d w (priceFiltrationSignatureSpace_of_market mkt) := by
  sorry

end SignatureVolatility
