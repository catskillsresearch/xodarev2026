module

public import SignatureVolatility.Letter
public import SignatureVolatility.Word


@[expose] public section

namespace SignatureVolatility

def pureBrownianWord (n : ℕ) : Word 2 :=
  List.replicate n ((0 : Fin 1).succ)

end SignatureVolatility
