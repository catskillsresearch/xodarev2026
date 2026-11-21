module

public import SignatureVolatility.PriceFiltrationSignatureSpace


@[expose] public section

noncomputable section

namespace SignatureVolatility

namespace PriceFiltrationSignatureSpace

variable {H_S : Type*} [NormedAddCommGroup H_S] [InnerProductSpace ℝ H_S] [CompleteSpace H_S]
  {d : ℕ}

def V_infty (PFS : PriceFiltrationSignatureSpace H_S d) : Submodule ℝ H_S :=
  Submodule.topologicalClosure (Submodule.span ℝ (Set.range PFS.Y))

end PriceFiltrationSignatureSpace

end SignatureVolatility
