import SignatureVolatility.Letter
import SignatureVolatility.Word


open scoped BigOperators Classical ENNReal NNReal RealInnerProductSpace
open MeasureTheory Filter Topology Set

noncomputable section

namespace SignatureVolatility

def pureBrownianWord (n : ℕ) : Word 2 :=
  List.replicate n ((0 : Fin 1).succ)

end SignatureVolatility
