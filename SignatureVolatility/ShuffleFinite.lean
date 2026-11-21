import SignatureVolatility.ExtTensorAlgebra.ExtTensorAlgebra
import SignatureVolatility.Letter
import SignatureVolatility.Word
import SignatureVolatility.WordsOfLength
import SignatureVolatility.ExtTensorAlgebra.ShuffleBasis


open scoped BigOperators Classical ENNReal NNReal RealInnerProductSpace
open MeasureTheory Filter Topology Set

noncomputable section

namespace SignatureVolatility

def shuffleFinite {d : ℕ} (a b : ExtTensorAlgebra (d + 1)) (supportBound : ℕ) :
    ExtTensorAlgebra (d + 1) :=
  ⟨fun K =>
    ∑ m ∈ Finset.range (supportBound + 1),
      ∑ n ∈ Finset.range (supportBound + 1),
        ∑ I ∈ wordsOfLength (d + 1) m,
          ∑ J ∈ wordsOfLength (d + 1) n,
            a.coeff I * b.coeff J * (ExtTensorAlgebra.shuffleBasis I J).coeff K⟩

end SignatureVolatility
