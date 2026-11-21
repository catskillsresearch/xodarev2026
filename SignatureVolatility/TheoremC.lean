module

public import SignatureVolatility.PriceFiltrationSignatureSpace.OfMarket
public import SignatureVolatility.TheoremCOfMarketKit


@[expose] public section

open MeasureTheory Set

namespace SignatureVolatility

/-- **Paper Theorem C.** Completeness depth characterisation over a market. -/
theorem theorem_C
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    (mkt : MarketData Ω P)
    {𝒦₁ 𝒦₂ : Set ℝ} (h𝒦₁ : Ioi (0 : ℝ) ⊆ closure 𝒦₁) (h𝒦₂ : Ioi (0 : ℝ) ⊆ closure 𝒦₂) :
    (∀ N : ℕ,
      (priceFiltrationSignatureSpace_of_market mkt).IsCompleteOnPriceFiltration 𝒦₁ N ↔
        (priceFiltrationSignatureSpace_of_market mkt).completenessDepth ≤ (N : ℕ∞)) ∧
    (∀ M : ℕ,
      (M : ℕ∞) < (priceFiltrationSignatureSpace_of_market mkt).completenessDepth →
        ¬ (priceFiltrationSignatureSpace_of_market mkt).IsCompleteOnPriceFiltration 𝒦₁ M) ∧
    (∀ N : ℕ,
      (priceFiltrationSignatureSpace_of_market mkt).IsCompleteOnPriceFiltration 𝒦₁ N ↔
        (priceFiltrationSignatureSpace_of_market mkt).IsCompleteOnPriceFiltration 𝒦₂ N) :=
  theorem_C_of_Market_Kit (priceFiltrationSignatureSpace_of_market mkt) h𝒦₁ h𝒦₂

end SignatureVolatility
