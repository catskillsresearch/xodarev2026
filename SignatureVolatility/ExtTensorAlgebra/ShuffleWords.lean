module

public import SignatureVolatility.Letter
public import SignatureVolatility.Word


@[expose] public section

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
