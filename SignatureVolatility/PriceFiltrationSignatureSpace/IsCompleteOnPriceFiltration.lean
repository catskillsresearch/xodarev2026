module

public import SignatureVolatility.PriceFiltrationSignatureSpace
public import SignatureVolatility.PriceFiltrationSignatureSpace.AugmentedMarketSpan


@[expose] public section

noncomputable section

namespace SignatureVolatility

namespace PriceFiltrationSignatureSpace

variable {H_S : Type*} [NormedAddCommGroup H_S] [InnerProductSpace ℝ H_S] [CompleteSpace H_S]
  {d : ℕ}

def IsCompleteOnPriceFiltration (PFS : PriceFiltrationSignatureSpace H_S d)
    (𝒦 : Set ℝ) (N : ℕ) : Prop :=
  (PFS.augmentedMarketSpan 𝒦 N).topologicalClosure = ⊤

end PriceFiltrationSignatureSpace

end SignatureVolatility
