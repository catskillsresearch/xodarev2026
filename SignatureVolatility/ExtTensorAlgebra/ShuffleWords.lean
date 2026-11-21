import SignatureVolatility.Letter
import SignatureVolatility.Word


open scoped BigOperators Classical ENNReal NNReal RealInnerProductSpace
open MeasureTheory Filter Topology Set

noncomputable section

namespace SignatureVolatility

namespace ExtTensorAlgebra

def shuffleWords {d : ℕ} : Word d → Word d → List (Word d)
  | [], J => [J]
  | i :: I, [] => [i :: I]
  | i :: I, j :: J =>
    (shuffleWords I (j :: J)).map (i :: ·) ++ (shuffleWords (i :: I) J).map (j :: ·)
termination_by I J => I.length + J.length

end ExtTensorAlgebra

end SignatureVolatility
