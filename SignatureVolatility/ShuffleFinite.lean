module

public import SignatureVolatility.ExtTensorAlgebra.ExtTensorAlgebra
public import SignatureVolatility.WordsOfLength
public import SignatureVolatility.ExtTensorAlgebra.ShuffleBasis


@[expose] public section

noncomputable section

namespace SignatureVolatility

/-- The shuffle product `a ⧢ b` restricted to pairs of words `I, J` of length at most
`supportBound`: `∑_{|I|, |J| ≤ supportBound} a_I b_J (e_I ⧢ e_J)`. -/
def shuffleFinite {d : ℕ} (a b : ExtTensorAlgebra (d + 1)) (supportBound : ℕ) :
    ExtTensorAlgebra (d + 1) :=
  ⟨fun K =>
    ∑ m ∈ Finset.range (supportBound + 1),
      ∑ n ∈ Finset.range (supportBound + 1),
        ∑ I ∈ wordsOfLength (d + 1) m,
          ∑ J ∈ wordsOfLength (d + 1) n,
            a.coeff I * b.coeff J * (ExtTensorAlgebra.shuffleBasis I J).coeff K⟩

end SignatureVolatility
