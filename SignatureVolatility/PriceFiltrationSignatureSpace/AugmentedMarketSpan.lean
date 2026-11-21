import SignatureVolatility.PriceFiltrationSignatureSpace


noncomputable section

namespace SignatureVolatility

namespace PriceFiltrationSignatureSpace

variable {H_S : Type*} [NormedAddCommGroup H_S] [InnerProductSpace ℝ H_S] [CompleteSpace H_S]
  {d : ℕ}

def augmentedMarketSpan (PFS : PriceFiltrationSignatureSpace H_S d) (𝒦 : Set ℝ) (N : ℕ) :
    Submodule ℝ H_S :=
  PFS.dynamicGainSubspace ⊔
    Submodule.span ℝ ((PFS.callPayoff '' 𝒦) ∪ {PFS.Y I | (I : Word (d + 1)) (_ : I.length ≤ N)})

end PriceFiltrationSignatureSpace

end SignatureVolatility
