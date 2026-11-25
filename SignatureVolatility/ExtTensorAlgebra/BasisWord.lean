module

public import SignatureVolatility.ExtTensorAlgebra.ExtTensorAlgebra
public import SignatureVolatility.ExtTensorAlgebra.IsFinitelySupported

@[expose] public section

noncomputable section

namespace SignatureVolatility

namespace ExtTensorAlgebra

/-- The basis element `e_I`: coefficient `1` at the word `I` and `0` elsewhere. -/
def basisWord {d : ℕ} (I : Word d) : ExtTensorAlgebra d :=
  ⟨fun J => if J = I then 1 else 0⟩

namespace basisWord

lemma isFinitelySupported {d : ℕ} (I : Word d) :
    IsFinitelySupported (basisWord I) := by
  refine ⟨I.length, fun J hJ => ?_⟩
  have hne : J ≠ I := fun h => by subst h; exact lt_irrefl _ hJ
  simp [basisWord, hne]

end basisWord

end ExtTensorAlgebra

end SignatureVolatility
