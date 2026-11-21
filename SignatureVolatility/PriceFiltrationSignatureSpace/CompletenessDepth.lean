import SignatureVolatility.PriceFiltrationSignatureSpace
import SignatureVolatility.PriceFiltrationSignatureSpace.VInfty
import SignatureVolatility.PriceFiltrationSignatureSpace.VSubspace

noncomputable section

namespace SignatureVolatility

namespace PriceFiltrationSignatureSpace

variable {H_S : Type*} [NormedAddCommGroup H_S] [InnerProductSpace ℝ H_S] [CompleteSpace H_S]
  {d : ℕ}

def completenessDepth (PFS : PriceFiltrationSignatureSpace H_S d) : ℕ∞ :=
  sInf {(N : ℕ∞) | ∃ n : ℕ, (N = (n : ℕ∞)) ∧ (PFS.V_subspace n).topologicalClosure = PFS.V_infty}

end PriceFiltrationSignatureSpace

end SignatureVolatility