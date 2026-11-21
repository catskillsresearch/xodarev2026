import SignatureVolatility.Letter
import SignatureVolatility.Word

namespace SignatureVolatility

def pureBrownianWord (n : ℕ) : Word 2 :=
  List.replicate n ((0 : Fin 1).succ)

end SignatureVolatility