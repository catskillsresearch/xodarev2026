module

public import SignatureVolatility.ProlongedBrownianSetup
public import SignatureVolatility.IndexedFiltration


@[expose] public section

open MeasureTheory

noncomputable section

namespace SignatureVolatility

/-- The price filtration `ℱ^S_t = σ(S_u : 0 ≤ u ≤ t)`. -/
def priceFiltration {Ω : Type*} [MeasurableSpace Ω]
    (S : ℝ → Ω → ℝ) (hS_meas : ∀ t, Measurable (S t)) : IndexedFiltration Ω :=
  generatedFiltration (fun t (_ : Unit) ω => S t ω) (fun t _ => hS_meas t)

end SignatureVolatility
