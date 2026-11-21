import SignatureVolatility.ProlongedBrownianSetup
import SignatureVolatility.IndexedFiltration

open MeasureTheory

noncomputable section

namespace SignatureVolatility

def priceFiltration {Ω : Type*} [MeasurableSpace Ω]
    (S : ℝ → Ω → ℝ) (hS_meas : ∀ t, Measurable (S t)) : IndexedFiltration Ω :=
  generatedFiltration (fun t (_ : Unit) ω => S t ω) (fun t _ => hS_meas t)

end SignatureVolatility
